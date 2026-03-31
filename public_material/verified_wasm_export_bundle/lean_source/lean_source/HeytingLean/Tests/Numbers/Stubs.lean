import HeytingLean.Numbers.SurrealCore
import HeytingLean.Numbers.Surreal.GameN
import HeytingLean.Numbers.Surreal.Nucleus
import HeytingLean.Numbers.Surreal.Equiv
import HeytingLean.Numbers.Surreal.Order
import HeytingLean.Numbers.OrdinalVN
import HeytingLean.Numbers.Ordinal.Nucleus
import HeytingLean.Computing.CircuitClassic
import HeytingLean.LoF.Instances

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Numbers
open HeytingLean.Computing

-- Surreal pre-game smoke checks
#check SurrealCore.PreGame
#check SurrealCore.birthday
#check SurrealCore.truncate
#check SurrealCore.PreGame.maxBirth
#check SurrealCore.PreGame.build
#check SurrealCore.legal
#check SurrealCore.close

-- Rank-indexed games
#check Numbers.Surreal.GameN
#check Numbers.Surreal.Game
#check Numbers.Surreal.Game.day
#check Numbers.Surreal.Game.L
#check Numbers.Surreal.Game.R
#check Numbers.Surreal.leAtN
#check Numbers.Surreal.leN
#check Numbers.Surreal.ltN
#check Numbers.Surreal.legalN
#check Numbers.Surreal.Game.L_zero
#check Numbers.Surreal.Game.R_zero

-- Surreal nucleus over sets of pre-games
#check Numbers.Surreal.Core.J
#check Numbers.Surreal.Core.canonImage

-- Canonical equivalence and quotient
#check Numbers.Surreal.approx
#check Numbers.Surreal.approxSetoid
#check Numbers.Surreal.SurrealQ
#check Numbers.Surreal.leQ
#check Numbers.Surreal.canonicalizeQ
#check SurrealCore.legal
#check SurrealCore.canonicalize

-- Ordinal vN smoke checks
#check Numbers.V
#check Numbers.V.shape
#check Numbers.rankOf

-- Ordinal nucleus
#check Numbers.Ordinal.J

-- Circuit smoke checks
#check Computing.Gate
#check Computing.Port
#check Computing.Circuit
#check Computing.CircuitClassic.normalize
#check Computing.CircuitClassic.normalize_seq
#check Computing.CircuitClassic.normalize_par
#check Computing.CircuitClassic.depth
#check Computing.CircuitClassic.occamByDepth
#check Computing.CircuitClassic.synthPar
#check Computing.CircuitClassic.synthSeq
#check Computing.CircuitClassic.Sem.gate
#check Computing.CircuitClassic.Sem.eval

-- Arithmetic skeleton
#check SurrealCore.add
#check SurrealCore.neg
#check SurrealCore.mul

-- PrimaryAlgebra instance on sets of pre-games
#check (inferInstance : HeytingLean.LoF.PrimaryAlgebra (Set SurrealCore.PreGame))

end Numbers
end Tests
end HeytingLean
