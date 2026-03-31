import HeytingLean.MirandaDynamics.Seismic.Basic
import HeytingLean.MirandaDynamics.Seismic.Observable
import HeytingLean.MirandaDynamics.Seismic.Reaching
import HeytingLean.MirandaDynamics.Seismic.Validation
import HeytingLean.MirandaDynamics.Seismic.Categorical
import HeytingLean.MirandaDynamics.Seismic.CategoricalValidation

/-!
# MirandaDynamics.Seismic (umbrella)

An observation-first physical-system integration target using real-world seismic data.

- basic types: stations/events/waveforms,
- an observation-window kernel operator,
- a TKFT reaching relation induced by detection,
- an offline threshold-based arrival detector.

The data acquisition bridge is `scripts/seismic_bridge.py`.
The offline validator executable is `seismic_validate_demo`.
-/
