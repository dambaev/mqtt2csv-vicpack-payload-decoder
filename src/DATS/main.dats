
#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0

#define LIBS_targetloc "../libs" (* search path for external libs *)
staload BS="{$LIBS}/ats-bytestring/SATS/bytestring.sats"
staload "{$LIBS}/ats-bytestring/SATS/bytestring.sats" (* overload operators *)
staload Vicpack="{$LIBS}/ats-vicpack/src/SATS/vicpack.sats"
staload B64="{$LIBS}/ats-base64/SATS/ats-base64.sats"

#define HX_LIBJANSSON_targetloc "$PATSHOME/contrib/atscntrb/atscntrb-hx-libjansson"
staload JSON="{$HX_LIBJANSSON}/SATS/jansson.sats"

%{

#include "poll.h" // pollfd
#include "sys/ioctl.h" // ioctl
#include "unistd.h" // posix

%}
%{
#define BAND(a,b) ((a) & (b))
%}
extern
fn band
  ( a: sint
  , b: sint
  ): sint = "mac#BAND"
  

typedef pollfd_t = $extype_struct"struct pollfd" of
{ fd = int
, events = sint
, revents = sint
}

extern
val POLLIN:sint = "mac#POLLIN"
extern
val POLLERR:sint = "mac#POLLERR"
typedef nfds_t = $extype"nfds_t"

extern
fn poll
  { n: pos}{l:agz}
  ( fds_pf: !array_v(pollfd_t, l, n)
  | fds: ptr l
  , nfds: size_t n
  , timeout: int
  ) : int = "mac#"

extern
val FIONREAD:int = "mac#FIONREAD"

extern
fn get_fd_pending_bytes
   ( socket: int
   ): size_t
implement get_fd_pending_bytes(socket) = res where {
   var res: size_t = i2sz 0
   val _ = $extfcall( size_t, "ioctl", socket, FIONREAD, addr@res)
}
extern
fn read
  {a: t0ype | sizeof(a) == sizeof(char) || sizeof(a) == sizeof(uchar) }{n: nat}{l:agz}
  ( pf: !array_v( a?, l, n) >> array_v(a, l, n)
  | fd: int
  , ptr l
  , sz: size_t n
  ): ssize_t = "mac#"

fn
  handle_payload
  ( i: !$BS.Bytestring0
  ):
  List0_vt( $Vicpack.Vicpack) =
let
  val i_sz = $BS.length i
in
  ifcase
  | i_sz < 4 => list_vt_nil()
  | i_sz <> i2sz 4 * ( i_sz / i2sz 4) => list_vt_nil()
  | _ =>
  let
    prval _ = $BS.lemma_bytestring_param(i)
    val ( pf | p, sz) = $BS.bs2bytes(i)
    val p_s = ptr2str( pf | p, sz) where {
      extern castfn
        ptr2str
        {n:nat}{l:addr}
        ( !array_v(byte, l, n) 
        | ptr l
        , size_t n
        ):<> string(n)
    }
  in
    case+ $B64.decode1( p_s, sz) of
    | ~None_vt() => list_vt_nil() where {
      prval () = $BS.bytes_addback( pf | i)
    }
    | ~Some_vt( decoded0) =>
    let
      val ( arr, cap, sz) = decoded0
    in
      if sz < 6
      then list_vt_nil() where {
        val () = arrayptr_free arr
        prval () = $BS.bytes_addback( pf | i)
      }
      else result where {
        val ( arr_pf | arr_p) = arrayptr_takeout_viewptr arr
        var decoded: $BS.Bytestring0?
        val () = decoded := $BS.pack( arr_pf | arr_p, sz, cap)
        val result = $Vicpack.parse decoded
        val () = $BS.free( arr_pf | decoded)
        prval () = arrayptr_addback( arr_pf | arr)
        val () = arrayptr_free arr
        prval () = $BS.bytes_addback( pf | i)
      }
    end
  end
end

fn
  {a:viewt0ype}{env0:viewt0ype}
  list_vt_freelin_funenv
  {fe:eff}{n:nat}
  ( l: list_vt( a, n)
  , env: &env0 >> _
  , f: ( &env0 >> _, a ) -<fe> void
  ):<!wrt,fe>
  void = loop( l, env, f) where {
  fun
    loop
    {n:nat}
    .<n>.
    ( l: list_vt(a, n)
    , env: &env0 >> _
    , f: ( &env0 >> _, a)-<fe> void
    ):<!wrt,fe>
    void =
    case+ l of
    | ~list_vt_nil() => ()
    | ~list_vt_cons( head, tail) => loop( tail, env, f) where {
      val () = f( env, head)
    }
}

fn
  is_vicotee
  ( s: !Strptr1
  ): bool = true

fn
  make_values
  {n:nat}
  (i: list_vt( $Vicpack.Vicpack, n)
  ): $BS.Bytestring0 = loop(i, acc) where {
  var acc: $BS.Bytestring0
  val () = acc := $BS.empty()
  fun
    loop
    {n:nat}
    ( xs: list_vt( $Vicpack.Vicpack, n)
    , acc: $BS.BytestringNSH0
    ): $BS.Bytestring0 =
  case+ xs of
  | ~list_vt_nil() => acc
  | ~list_vt_cons( head, tail) =>
    case+ head of
    | ~$Vicpack.temperature_vt( v) => loop( tail, result) where {
      val (pf, fpf | p) = array_ptr_alloc<uchar>(i2sz 100)
      val _ = $extfcall( int, "sprintf", p, "%f\t", v)
      val sz = g1ofg0( $extfcall( size_t, "strlen", p))
      val () = assertloc( sz <= i2sz 100)
      val result = acc + $BS.pack( pf, fpf | p, sz, i2sz 100)
    }
    | ~$Vicpack.humidity_vt( v) => loop( tail, result) where {
      val (pf, fpf | p) = array_ptr_alloc<uchar>(i2sz 100)
      val _ = $extfcall( int, "sprintf", p, "%i\t", v)
      val sz = g1ofg0($extfcall( size_t, "strlen", p))
      val () = assertloc( sz <= i2sz 100)
      val result = acc + $BS.pack( pf, fpf | p, sz, i2sz 100)
    }
    | any => loop( tail, acc) where {
      val () = $Vicpack.free any
    }
}

fn
  json_object_get
  {l1:agz}
  ( i: !$JSON.JSONptr l1
  , s: string
  ):
  Option_vt( [l2:agz] vtget1( $JSON.JSONptr(l1), $JSON.JSONptr(l2))) =
let
  val ( pf | p) = $JSON.json_object_get( i, s)
in
  if $JSON.JSONptr_is_null p
  then None_vt() where {
    prval () = minus_addback( pf, p | i)
  }
  else Some_vt( (pf | p))
end

fn
  json_bytestring_value
  {l:agz}
  ( i: !$JSON.JSONptr l
  , s: string
  ):
  Option_vt( $BS.BytestringNSH0) =
case+ json_object_get( i, s) of
| ~None_vt() => None_vt()
| ~Some_vt( @( pf | p)) =>
let
  val (v_pf | v) = $JSON.json_string_value( p)
  val bs0 = $BS.pack( g1ofg0(strptr2str(v))) where {
    extern castfn strptr2str( v: !Strptr1): string
  }
  val bs = copy bs0
  val () = $BS.free( bs0)
  prval () = minus_addback( v_pf, v | p)
  prval () = minus_addback( pf, p | i)
in
  Some_vt( bs)
end

fn
  uint322bs 
  ( i: uint32
  ): $BS.BytestringNSH1 = result where {
  val (pf, fpf | p) = array_ptr_alloc<uchar>(i2sz 100)
  val _ = $extfcall( int, "sprintf", p, "%u", i)
  val sz = g1ofg0( $extfcall( size_t, "strlen", p))
  val () = assertloc( sz <= i2sz 100)
  val () = assertloc( sz > i2sz 0)
  val result = $BS.pack( pf, fpf | p, sz, i2sz 100)
}
fn
  double2bs
  ( i: double
  ): $BS.BytestringNSH1 = result where {
  val (pf, fpf | p) = array_ptr_alloc<uchar>(i2sz 100)
  val _ = $extfcall( int, "sprintf", p, "%f", i)
  val sz = g1ofg0( $extfcall( size_t, "strlen", p))
  val () = assertloc( sz <= i2sz 100)
  val () = assertloc( sz > i2sz 0)
  val result = $BS.pack( pf, fpf | p, sz, i2sz 100)
}


fn
  get_temperature_humidity
  (vi: !$BS.Bytestring0
  ): Option_vt( @( $BS.BytestringNSH0, $BS.BytestringNSH0)) =
let
  var i: $BS.Bytestring0?
  val () = i := vi
in
if $BS.length i < 6
then None_vt() where {
  prval () = vi := i
}
else
case+ $Vicpack.parse i of
| ~list_vt_nil() => None_vt() where {
  prval () = vi := i
}
| packages => walk_packages( packages, (None_vt(), None_vt())) where {
  prval () = vi := i
  fun
    walk_packages
    {n:nat}
    .<n>.
    ( xs: list_vt( $Vicpack.Vicpack, n)
    , acc: (Option_vt( $BS.BytestringNSH0), Option_vt( $BS.BytestringNSH0))
    ): Option_vt( @($BS.BytestringNSH0, $BS.BytestringNSH0)) =
  case+ xs of
  | ~list_vt_nil() =>
    ( case- acc of
    | @(~None_vt(), ~None_vt())=> None_vt()
    | @(~None_vt(), ~Some_vt(h))=> Some_vt( ($BS.pack "", h))
    | @(~Some_vt(t), ~None_vt()) => Some_vt( (t, $BS.pack ""))
    | @(~Some_vt(t), ~Some_vt(h)) => Some_vt( (t, h))
    )
  | ~list_vt_cons( head, tail) =>
    ( case- acc of
    | @( ~Some_vt(t), ~Some_vt(h)) => walk_packages( tail, (Some_vt(t), Some_vt(h))) where {
      val () = $Vicpack.free head
    }
    | @(~None_vt(), some) => 
      ( case+ head of
      | ~$Vicpack.temperature_vt(t) => walk_packages( tail, (Some_vt(double2bs t), some))
      | _ => walk_packages( tail, (None_vt(), some)) where {
        val () = $Vicpack.free head
      }
      )
    | @(some, ~None_vt()) =>
      ( case+ head of
      | ~$Vicpack.humidity_vt(h) => walk_packages( tail, (some, Some_vt(uint322bs h)))
      | _ => walk_packages( tail, (some, None_vt())) where {
        val () = $Vicpack.free head
      }
      )
    )
}
end

fn
  handle_line
  ( i: !$BS.Bytestring0
  ): void =
let
  prval () = lemma_bytestring_param( i)
in
  if $BS.length i = 0
  then ()
  else {
    var jsonerr: $JSON.json_err
    val ( pf | p, sz) = $BS.bs2bytes( i)
    val root = $JSON.json_loadb( pf | p, sz, 0, jsonerr)
    val () = $JSON.json_decref( root) where {
      val () =
        if $JSON.JSONptr_isnot_null root
        then
        case+ json_object_get( root, "metadata") of
        | ~None_vt() => ()
        | ~Some_vt( @(meta_pf | meta_p ) ) => {
        val otime_bs = json_bytestring_value( meta_p, "time")
        prval () = minus_addback( meta_pf, meta_p | root)
        val ohws = json_bytestring_value( root, "hardware_serial")
        val orawpayload = json_bytestring_value( root, "payload_raw")
        val () =
          case+ (otime_bs,ohws,orawpayload) of
          | (~None_vt(), _, _) => () where {
            val () =
              case+ ohws of
              | ~None_vt() => ()
              | ~Some_vt(bs) => $BS.free( bs)
            val () =
              case+ orawpayload of
              | ~None_vt() => ()
              | ~Some_vt(bs) => $BS.free(bs)
          }
          | (_, ~None_vt(), _) => () where {
            val () =
              case+ otime_bs of
              | ~None_vt() => ()
              | ~Some_vt(bs) => $BS.free( bs)
            val () =
              case+ orawpayload of
              | ~None_vt() => ()
              | ~Some_vt(bs) => $BS.free(bs)
          }
          | (_, _, ~None_vt()) => () where {
            val () =
              case+ ohws of
              | ~None_vt() => ()
              | ~Some_vt(bs) => $BS.free( bs)
            val () =
              case+ otime_bs of
              | ~None_vt() => ()
              | ~Some_vt(bs) => $BS.free(bs)
          }
          | (~Some_vt( time), ~Some_vt(hws), ~Some_vt(rawpayload)) =>
            case+ get_temperature_humidity( rawpayload) of
            | ~None_vt() => {
              val () = $BS.free( time)
              val () = $BS.free( hws)
              val () = $BS.free( rawpayload)
            }
            | ~Some_vt( @(temperature, humidity)) => {
              val () = $BS.printlnC( time
                                  + $BS.pack "\t"
                                  + hws
                                  + $BS.pack "\t"
                                  + temperature
                                  + $BS.pack "\t"
                                  + humidity
                                  )
              val () = $BS.free( rawpayload)
            }
        } // meta
        else () // root
    }
    prval () = $BS.bytes_addback( pf | i)
  }
end


fn
  handle_lines
  ( i: &$BS.BytestringNSH0 >> $BS.BytestringNSH0
  ): void = 
let
  prval () = lemma_bytestring_param( i)
  var lines: List_vt( $BS.Bytestring0)?
  val () = lines := $BS.split_on( c2uc '\n', i)
  val last_idx = list_vt_length lines
in
  ifcase
  | last_idx = 0 => {
    val+ ~list_vt_nil() = lines
  }
  | last_idx = 1 => {
    val+ ~list_vt_cons(head, tail) = lines
    val+ ~list_vt_nil() = tail
    val () = println!("no newline detected in the input, appending input to old leftovers")
    val () = $BS.free( head, i)
  }
  | _ => i := last where {
    var last: $BS.Bytestring0?
    val () = last := list_vt_takeout_at( lines, last_idx - 1)
    val () = cleaner( lines, i) where {
      fun
        cleaner
        {n, cap, ucap, refcnt, elen, eoffset:nat | refcnt > n}{dynamic:bool}{l:addr}
        .<n>.
        ( xs: list_vt( [len, offset:nat] $BS.Bytestring_vtype( len, offset, cap, 0, 1, dynamic, l), n)
        , env: &$BS.Bytestring_vtype( elen, eoffset, cap, ucap, refcnt, dynamic, l) >> $BS.Bytestring_vtype( elen, eoffset, cap, ucap, refcnt - n, dynamic, l)
        ):
        void =
      case+ xs of
      | ~list_vt_nil() => ()
      | ~list_vt_cons( head, tail) =>
        if $BS.length head > 0
        then cleaner( tail, env) where {
          val () = handle_line( head)
          val () = $BS.free( head, env)
        }
        else cleaner( tail, env) where {
          val () = $BS.free( head, env)   
        }
    }
    val () = $BS.free( i, last)
  }
  
end

fun
  loop
  {n:nat | n > 0}{l:agz}
  ( fds_pf: !array_v(pollfd_t, l, n)
  | buf: &$BS.BytestringNSH0 >> _
  , fds: ptr l
  , fds_sz: size_t n
  ): void =
case+ poll( fds_pf | fds, fds_sz, ~1) of
| some when some = (~1) => loop( fds_pf | buf, fds, fds_sz) where {
  val () = println!("timeouted")
}
| 0 => loop( fds_pf | buf, fds, fds_sz) where {
  val () = println!("interrupted")
}
| fds_available =>
let
  prval (pf1, pf2) = array_v_uncons( fds_pf)
  val pollfd = !fds
  prval () = fds_pf := array_v_cons( pf1, pf2)
in
  if band( pollfd.revents, POLLIN) <> POLLIN
  then handle_line( buf) (* process the rest and exit *)
  else loop (fds_pf | buf, fds, fds_sz) where {
    val available = g1ofg0( get_fd_pending_bytes( pollfd. fd))
    val ( pf, fpf | p) = array_ptr_alloc<uchar>( available)
    val readed = read{uchar}( pf | 0, p, available)
    var newinput: $BS.Bytestring0?
    val () = newinput := $BS.pack( pf, fpf | p, available, available)
    val () = buf := buf + newinput
    val () = handle_lines( buf)
  }
end

implement main0() = {
  var buf: $BS.Bytestring0?
  val () = buf := $BS.empty()
  val ( pf, fpf | p) = array_ptr_alloc<pollfd_t>(i2sz 1)
  prval () = initialize{pollfd_t}(pf) where {
    extern prval initialize
      {a:t0ype}{l:addr}{n:nat}
      ( pf: !array_v( a?, l, n) >> array_v(a,l,n)
      ): void
  }
  prval (pf1, pf2) = array_v_uncons pf
  val () = !p := (@{ fd = g0ofg1 0, events = POLLIN, revents = g0int2int_int_sint 0}:pollfd_t)
  prval () = pf := array_v_cons( pf1, pf2)
  val () = loop( pf | buf, p, i2sz 1)
  val () = array_ptr_free( pf, fpf | p)
  val () = $BS.free buf
}