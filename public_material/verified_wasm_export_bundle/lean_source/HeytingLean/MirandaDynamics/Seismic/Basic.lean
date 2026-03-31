/-!
# MirandaDynamics.Seismic: basic types

This folder provides an *observation-first* physical-system integration target for the TKFT
reaching semantics.

We intentionally separate:

- **data** (stations/events/waveforms), which we can represent directly, from
- **physics claims** (travel times, attenuation, wave equation), which will be introduced only as
  explicit interfaces/structures elsewhere.

The corresponding data acquisition bridge lives in `scripts/seismic_bridge.py`.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Seismic

/-- A seismic station with known coordinates.

All numeric fields are kept as `Float` for practical JSON interoperability.
-/
structure Station where
  network : String
  code : String
  latitude : Float
  longitude : Float
  elevation_m : Float
  deriving Repr

namespace Station

def key (s : Station) : String :=
  s!"{s.network}.{s.code}"

end Station

/-- A time window for an observation, expressed in Unix time (milliseconds). -/
structure ObservationWindow where
  start_time_ms : Int
  duration_ms : Int
  deriving Repr

/-- Raw waveform data from a station for a fixed window.

This is deliberately a “thin” container around samples + timing metadata.
-/
structure Waveform where
  station : Station
  window : ObservationWindow
  samples : Array Float
  sample_rate_hz : Float
  deriving Repr

/-- A seismic event (earthquake/explosion) in a simplified form.

This is designed to match the USGS GeoJSON feed fields used in `scripts/seismic_bridge.py`.
-/
structure SeismicEvent where
  id : String
  time_ms : Int
  latitude : Float
  longitude : Float
  depth_km : Float
  magnitude : Float
  place : String
  deriving Repr

end Seismic
end MirandaDynamics
end HeytingLean

