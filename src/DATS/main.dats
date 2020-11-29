
#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0

#define LIBS_targetloc "../libs" (* search path for external libs *)

#include "{$LIBS}/ats-bytestring/HATS/bytestring.hats" (* overload operators *)
staload BS="{$LIBS}/ats-bytestring/SATS/bytestring.sats"

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
  {a: t0ype | sizeof(a) == sizeof(char) || sizeof(a) == sizeof(uchar) || sizeof(a) == sizeof(byte) }{n: nat}{l:agz}
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
  uint162bs 
  ( i: uint16
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
  uc2bs
  ( i: uchar
  ): $BS.BytestringNSH1 = result where {
  val (pf, fpf | p) = array_ptr_alloc<uchar>(i2sz 100)
  val _ = $extfcall( int, "sprintf", p, "%i", i)
  val sz = g1ofg0( $extfcall( size_t, "strlen", p))
  val () = assertloc( sz <= i2sz 100)
  val () = assertloc( sz > i2sz 0)
  val result = $BS.pack( pf, fpf | p, sz, i2sz 100)
}


fn
  get_temperature_humidity
  (vi: !$BS.Bytestring0
  ):
  Option_vt( @( $BS.BytestringNSH1 // temperature
              , $BS.BytestringNSH1 // humidity
              , $BS.BytestringNSH1 // voc_iaq
              , $BS.BytestringNSH1 // voc_temperature
              , $BS.BytestringNSH1 // voc_humidity
              , $BS.BytestringNSH1 // voc_pressure
              , $BS.BytestringNSH1 // voc_ambient_light
              , $BS.BytestringNSH1 // voc_sound_peak
              , $BS.BytestringNSH1 // internal_battery
              )
           ) =
let
  var i: $BS.Bytestring0?
  val () = i := vi
  val i_sz = $BS.length i
in
ifcase
| $BS.length i < 4 => None_vt() where { prval () = vi := i }
| i_sz <> i2sz 4 * ( i_sz / i2sz 4) => None_vt() where { prval () = vi := i }
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
    | ~None_vt() => None_vt() where { 
      prval () = $BS.bytes_addback( pf | i)
      prval () = vi := i
    }
    | ~Some_vt( decoded0) =>
    let
      val ( arr, cap, sz) = decoded0
    in
        if sz < 6
        then None_vt() where {
          prval () = $BS.bytes_addback( pf | i)
          prval () = vi := i
          val () = arrayptr_free arr
        }
        else 
        let
          val ( arr_pf | arr_p) = arrayptr_takeout_viewptr arr
          var decoded: $BS.Bytestring0?
          val () = decoded := $BS.pack( arr_pf | arr_p, sz, cap)
          prval () = $BS.bytes_addback( pf | i)
          prval () = vi := i
        in
          case+ $Vicpack.parse decoded of
          | ~list_vt_nil() => None_vt() where {
            val () = println!("parse returned 0 elements")
            val () = $BS.free( arr_pf | decoded)
            prval () = arrayptr_addback( arr_pf | arr)
            val () = arrayptr_free arr
          }
          | packages => walk_packages( packages
                                     , ( None_vt()
                                       , None_vt()
                                       , None_vt()
                                       , None_vt()
                                       , None_vt()
                                       , None_vt()
                                       , None_vt()
                                       , None_vt()
                                       , None_vt()
                                       )
                                     ) where {
            val () = $BS.free( arr_pf | decoded)
            prval () = arrayptr_addback( arr_pf | arr)
            val () = arrayptr_free arr
            fun
              walk_packages
              {n:nat}
              .<n>.
              ( xs: list_vt( $Vicpack.Vicpack, n)
              , acc: ( Option_vt( $BS.BytestringNSH1)
                     , Option_vt( $BS.BytestringNSH1)
                     , Option_vt( $BS.BytestringNSH1)
                     , Option_vt( $BS.BytestringNSH1)
                     , Option_vt( $BS.BytestringNSH1)
                     , Option_vt( $BS.BytestringNSH1)
                     , Option_vt( $BS.BytestringNSH1)
                     , Option_vt( $BS.BytestringNSH1)
                     , Option_vt( $BS.BytestringNSH1)
                     )
              ): Option_vt( @( $BS.BytestringNSH1
                             , $BS.BytestringNSH1
                             , $BS.BytestringNSH1
                             , $BS.BytestringNSH1
                             , $BS.BytestringNSH1
                             , $BS.BytestringNSH1
                             , $BS.BytestringNSH1
                             , $BS.BytestringNSH1
                             , $BS.BytestringNSH1
                             )
                           ) =
            case+ xs of
            | ~list_vt_nil() =>
              ( case- acc of
              | @( ~None_vt()
                 , ~None_vt()
                 , ~None_vt()
                 , ~None_vt()
                 , ~None_vt()
                 , ~None_vt()
                 , ~None_vt()
                 , ~None_vt()
                 , ~None_vt()
                 )=> None_vt() (* some non-interesting package*)
              | @( temperature
                 , humidity
                 , voc_iaq
                 , voc_temperature
                 , voc_humidity
                 , voc_pressure
                 , voc_ambient_light
                 , voc_sound_peak
                 , internal_battery
                 ) => Some_vt( ( unopt temperature
                               , unopt humidity
                               , unopt voc_iaq
                               , unopt voc_temperature
                               , unopt voc_humidity
                               , unopt voc_pressure
                               , unopt voc_ambient_light
                               , unopt voc_sound_peak
                               , unopt internal_battery
                               )
                             ) where {
                 fn unopt( ov: Option_vt($BS.BytestringNSH1)):<!wrt> $BS.BytestringNSH1 =
                    case+ ov of
                    | ~None_vt() => $BS.pack "-"
                    | ~Some_vt(v) => v
                  }
              )
            | ~list_vt_cons( head, tail) =>
              ( case- acc of
              | @( o1 as Some_vt(_)
                 , o2 as Some_vt(_)
                 , o3 as Some_vt(_)
                 , o4 as Some_vt(_)
                 , o5 as Some_vt(_)
                 , o6 as Some_vt(_)
                 , o7 as Some_vt(_)
                 , o8 as Some_vt(_)
                 , o9 as Some_vt(_)
                 ) => walk_packages( tail, (o1, o2, o3, o4, o5, o6, o7, o8, o9)) where {
                val () = $Vicpack.free head
              }
              | @(o1, o2, o3, o4, o5, o6, o7, o8, o9) =>
                ( case+ head of
                | ~$Vicpack.temperature_vt(t) => walk_packages( tail, (Some_vt(double2bs t), o2, o3, o4, o5, o6, o7, o8, o9)) where {
                  val- ~None_vt() = o1
                }
                | ~$Vicpack.humidity_vt(h) => walk_packages( tail, (o1, Some_vt(uint322bs h), o3, o4, o5, o6, o7, o8, o9)) where {
                  val- ~None_vt() = o2
                }
                | ~$Vicpack.voc_iaq_vt( @{ state = state, index=index}) => walk_packages( tail, (o1, o2, Some_vt(iaq), o4, o5, o6, o7, o8, o9)) where {
                  val iaq = $BS.pack "state: " + uc2bs state + $BS.pack ", index: " + uint162bs index
                  val- ~None_vt() = o3
                }
                | ~$Vicpack.voc_temperature_vt(c) => walk_packages( tail, (o1, o2, o3, Some_vt(double2bs c), o5, o6, o7, o8, o9)) where {
                  val- ~None_vt() = o4
                }
                | ~$Vicpack.voc_humidity_vt(c) => walk_packages( tail, (o1, o2, o3, o4, Some_vt(double2bs c), o6, o7, o8, o9)) where {
                  val- ~None_vt() = o5
                }
                | ~$Vicpack.voc_pressure_vt(c) => walk_packages( tail, (o1, o2, o3, o4, o5, Some_vt(double2bs c), o7, o8, o9)) where {
                  val- ~None_vt() = o6
                }
                | ~$Vicpack.voc_ambient_light_vt(c) => walk_packages( tail, (o1, o2, o3, o4, o5, o6, Some_vt(double2bs c), o8, o9)) where {
                  val- ~None_vt() = o7
                }
                | ~$Vicpack.voc_sound_peak_vt(c) => walk_packages( tail, (o1, o2, o3, o4, o5, o6, o7, Some_vt(uint162bs c), o9)) where {
                  val- ~None_vt() = o8
                }
                | ~$Vicpack.internal_battery_vt(c) => walk_packages( tail, (o1, o2, o3, o4, o5, o6, o7, o8, Some_vt(double2bs c))) where {
                  val- ~None_vt() = o9
                }
                | _ => walk_packages( tail, (o1, o2, o3, o4, o5, o6, o7, o8, o9)) where {
                  val () = $Vicpack.free head
                }
                )
              )
          }
        end
    end
  end
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
            | ~Some_vt( @(temperature, humidity, voc_iaq, voc_temperature, voc_humidity, voc_pressure, voc_ambient_light, voc_sound_peak, internal_battery)) => {
              val () = assertloc( $BS.isnot_empty( time))
              val () = assertloc( $BS.isnot_empty( hws))
              val () = $BS.printlnC( time
                                  + $BS.pack "\t"
                                  + hws
                                  + $BS.pack "\t"
                                  + temperature
                                  + $BS.pack "\t"
                                  + humidity
                                  + $BS.pack "\t"
                                  + voc_iaq
                                  + $BS.pack "\t"
                                  + voc_temperature
                                  + $BS.pack "\t"
                                  + voc_humidity
                                  + $BS.pack "\t"
                                  + voc_pressure
                                  + $BS.pack "\t"
                                  + voc_ambient_light
                                  + $BS.pack "\t"
                                  + voc_sound_peak
                                  + $BS.pack "\t"
                                  + internal_battery
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
  else 
  let
    val available = g1ofg0( get_fd_pending_bytes( pollfd. fd))
  in
    if available <= 0
    then loop (fds_pf | buf, fds, fds_sz)
    else
      if $BS.isnot_empty buf
      then loop (fds_pf | buf, fds, fds_sz) where {
        val buf_sz = $BS.length buf
        val () = buf :=  $BS.create( buf_sz + available) ++ buf
        val ( pf | p, usz) = $BS.bs2unused_bytes buf
        val readed = read{byte}( pf | 0, p, available)
        val () = $BS.unused_bytes_addback( pf | buf, available)
        val () = handle_lines( buf)
      }
      else loop (fds_pf | buf, fds, fds_sz) where {
        val () = $BS.free buf
        val () = buf := $BS.create( available)
        val ( pf | p, usz) = $BS.bs2unused_bytes buf
        val readed = read{byte}( pf | 0, p, available)
        val () = $BS.unused_bytes_addback( pf | buf, available)
        val () = handle_lines( buf)
      }
  end
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
  val () = println!( "time"
                   , "\t"
                   , "serial number"
                   , "\t"
                   , "temperature"
                   , "\t"
                   , "humidity"
                   , "\t"
                   , "VOC_IAQ"
                   , "\t"
                   , "VOC_TEMPERATURE"
                   , "\t"
                   , "VOC_HUMIDITY"
                   , "\t"
                   , "VOC_PRESSURE"
                   , "\t"
                   , "VOC_AMBIENT"
                   , "\t"
                   , "VOC_SOUND_PEAK"
                   , "\t"
                   , "INTERNAL_BATTERY"
                   )
  val () = loop( pf | buf, p, i2sz 1)
  val () = array_ptr_free( pf, fpf | p)
  val () = $BS.free buf
}