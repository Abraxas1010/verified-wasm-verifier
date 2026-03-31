-- LeanSP: Lean-native Solidity Verification Prover
-- Root import file

-- Phase 1: Yul Frontend
import HeytingLean.LeanSP.Lang.YulSyntax
import HeytingLean.LeanSP.Lang.YulParser

-- Phase 2: Word256 + EVM State
import HeytingLean.LeanSP.Arith.Word256
import HeytingLean.LeanSP.Arith.SignedArith
import HeytingLean.LeanSP.Arith.Word256Props
import HeytingLean.LeanSP.Memory.EVMMemory
import HeytingLean.LeanSP.Memory.EVMStorage
import HeytingLean.LeanSP.Memory.EVMStack
import HeytingLean.LeanSP.Lang.EVMState
import HeytingLean.LeanSP.Lang.EVMPrimops

-- Phase 3: Yul Semantics
import HeytingLean.LeanSP.Lang.YulSemantics

-- Phase 4: Hoare Logic + VC
import HeytingLean.LeanSP.Verify.Hoare
import HeytingLean.LeanSP.Verify.Tactics
import HeytingLean.LeanSP.Verify.VCDischarge

-- Phase 5: Verified Contracts + CAB
import HeytingLean.LeanSP.RealWorld.SafeMathVerified
import HeytingLean.LeanSP.RealWorld.ERC20Verified
import HeytingLean.LeanSP.RealWorld.AccessControlVerified
import HeytingLean.LeanSP.RealWorld.EscrowVerified
import HeytingLean.LeanSP.RealWorld.SimpleVaultVerified
import HeytingLean.LeanSP.RealWorld.TokenVestingVerified
import HeytingLean.LeanSP.Pipeline.CABExport

-- Mapping slot verification
import HeytingLean.LeanSP.Memory.MappingSlot

-- External call model
import HeytingLean.LeanSP.ExternalCalls.CallSpec
import HeytingLean.LeanSP.ExternalCalls.CEIPattern
import HeytingLean.LeanSP.ExternalCalls.ReentrancyGuard

-- Pipeline
import HeytingLean.LeanSP.Pipeline.SolcInterface
import HeytingLean.LeanSP.Pipeline.ContractLoader
