import HeytingLean.LeanCP.Lang.CSemantics

namespace HeytingLean.LeanCP

theorem lookup_updateVarEnv_ne
    (env : Env) (x y : String) (v : CVal) (hxy : y ≠ x) :
    List.lookup y ((x, v) :: env.filter (fun p => p.1 != x)) = List.lookup y env := by
  induction env with
  | nil =>
      cases hyx : (y == x) with
      | true =>
          have : y = x := by simpa [beq_iff_eq] using hyx
          exact (hxy this).elim
      | false =>
          simp [List.lookup, hyx]
  | cons head tail ih =>
      rcases head with ⟨key, val⟩
      cases hyk : (y == key) with
      | true =>
          have : y = key := by simpa [beq_iff_eq] using hyk
          subst key
          cases hyx : (y == x) with
          | true =>
              have : y = x := by simpa [beq_iff_eq] using hyx
              exact (hxy this).elim
          | false =>
              have hkeep : (y != x) = true := by
                simpa [bne_iff_ne] using hxy
              simp [List.lookup, List.filter, hyx, hkeep]
      | false =>
          cases hkx : (key == x) with
          | true =>
              have : key = x := by simpa [beq_iff_eq] using hkx
              subst key
              cases hyx : (y == x) with
              | true =>
                  have : y = x := by simpa [beq_iff_eq] using hyx
                  exact (hxy this).elim
              | false =>
                  simpa [List.lookup, List.filter, hyk, hyx] using ih
          | false =>
              have hkxNe : key ≠ x := by
                simpa [beq_iff_eq] using hkx
              have hkeep : (key != x) = true := by
                simpa [bne_iff_ne] using hkxNe
              simpa [List.lookup, List.filter, hyk, hkeep] using ih

theorem lookupVar_updateVar_eq (st : CState) (x : String) (v : CVal) :
    (st.updateVar x v).lookupVar x = some v := by
  simp [CState.lookupVar, CState.updateVar]

theorem lookupVar_updateVar_ne (st : CState) (x y : String) (v : CVal)
    (hxy : y ≠ x) :
    (st.updateVar x v).lookupVar y = st.lookupVar y := by
  simpa [CState.lookupVar, CState.updateVar] using
    lookup_updateVarEnv_ne st.env x y v hxy

@[simp] theorem updateVar_heap (st : CState) (x : String) (v : CVal) :
    (st.updateVar x v).heap = st.heap := by
  rfl

@[simp] theorem updateVar_nextAddr (st : CState) (x : String) (v : CVal) :
    (st.updateVar x v).nextAddr = st.nextAddr := by
  rfl

@[simp] theorem updateVar_mem (st : CState) (x : String) (v : CVal) :
    (st.updateVar x v).mem = st.mem := by
  rfl

@[simp] theorem updateVar_allocs (st : CState) (x : String) (v : CVal) :
    (st.updateVar x v).allocs = st.allocs := by
  rfl

@[simp] theorem removeVar_heap (st : CState) (x : String) :
    (st.removeVar x).heap = st.heap := by
  rfl

@[simp] theorem removeVar_nextAddr (st : CState) (x : String) :
    (st.removeVar x).nextAddr = st.nextAddr := by
  rfl

@[simp] theorem removeVar_mem (st : CState) (x : String) :
    (st.removeVar x).mem = st.mem := by
  rfl

@[simp] theorem removeVar_allocs (st : CState) (x : String) :
    (st.removeVar x).allocs = st.allocs := by
  rfl

theorem heap_read_write_eq (h : Heap) (addr : Nat) (v : CVal) :
    (h.write addr v).read addr = some v := by
  simp [Heap.read, Heap.write, Finmap.lookup_insert]

theorem heap_read_write_ne (h : Heap) (addr1 addr2 : Nat) (v : CVal)
    (hne : addr2 ≠ addr1) :
    (h.write addr1 v).read addr2 = h.read addr2 := by
  simp [Heap.read, Heap.write, Finmap.lookup_insert_of_ne, hne]

@[simp] theorem enterBlockState_heap (st : CState) (decls : List (String × CType)) :
    (enterBlockState st decls).heap = st.heap := by
  induction decls generalizing st with
  | nil =>
      simp [enterBlockState]
  | cons d ds ih =>
      rcases d with ⟨x, ty⟩
      simpa [enterBlockState, CState.updateVar] using ih (st := st.updateVar x CVal.undef)

@[simp] theorem enterBlockState_nextAddr (st : CState) (decls : List (String × CType)) :
    (enterBlockState st decls).nextAddr = st.nextAddr := by
  induction decls generalizing st with
  | nil =>
      simp [enterBlockState]
  | cons d ds ih =>
      rcases d with ⟨x, ty⟩
      simpa [enterBlockState, CState.updateVar] using ih (st := st.updateVar x CVal.undef)

@[simp] theorem enterBlockState_allocs (st : CState) (decls : List (String × CType)) :
    (enterBlockState st decls).allocs = st.allocs := by
  induction decls generalizing st with
  | nil =>
      simp [enterBlockState]
  | cons d ds ih =>
      rcases d with ⟨x, ty⟩
      simpa [enterBlockState, CState.updateVar] using ih (st := st.updateVar x CVal.undef)

@[simp] theorem restoreBlockState_heap
    (before after : CState) (decls : List (String × CType)) :
    (restoreBlockState before after decls).heap = after.heap := by
  induction decls generalizing after with
  | nil =>
      simp [restoreBlockState]
  | cons d ds ih =>
      rcases d with ⟨x, ty⟩
      cases hlookup : before.lookupVar x with
      | none =>
          calc
            (restoreBlockState before after ((x, ty) :: ds)).heap
                = (restoreBlockState before (after.removeVar x) ds).heap := by
                    simp [restoreBlockState, hlookup]
            _ = (after.removeVar x).heap := ih (after := after.removeVar x)
            _ = after.heap := by simp
      | some v =>
          calc
            (restoreBlockState before after ((x, ty) :: ds)).heap
                = (restoreBlockState before (after.updateVar x v) ds).heap := by
                    simp [restoreBlockState, hlookup]
            _ = (after.updateVar x v).heap := ih (after := after.updateVar x v)
            _ = after.heap := by simp

@[simp] theorem restoreBlockState_nextAddr
    (before after : CState) (decls : List (String × CType)) :
    (restoreBlockState before after decls).nextAddr = after.nextAddr := by
  induction decls generalizing after with
  | nil =>
      simp [restoreBlockState]
  | cons d ds ih =>
      rcases d with ⟨x, ty⟩
      cases hlookup : before.lookupVar x with
      | none =>
          calc
            (restoreBlockState before after ((x, ty) :: ds)).nextAddr
                = (restoreBlockState before (after.removeVar x) ds).nextAddr := by
                    simp [restoreBlockState, hlookup]
            _ = (after.removeVar x).nextAddr := ih (after := after.removeVar x)
            _ = after.nextAddr := by simp
      | some v =>
          calc
            (restoreBlockState before after ((x, ty) :: ds)).nextAddr
                = (restoreBlockState before (after.updateVar x v) ds).nextAddr := by
                    simp [restoreBlockState, hlookup]
            _ = (after.updateVar x v).nextAddr := ih (after := after.updateVar x v)
            _ = after.nextAddr := by simp

@[simp] theorem restoreBlockState_mem
    (before after : CState) (decls : List (String × CType)) :
    (restoreBlockState before after decls).mem = after.mem := by
  induction decls generalizing after with
  | nil =>
      simp [restoreBlockState]
  | cons d ds ih =>
      rcases d with ⟨x, ty⟩
      cases hlookup : before.lookupVar x with
      | none =>
          calc
            (restoreBlockState before after ((x, ty) :: ds)).mem
                = (restoreBlockState before (after.removeVar x) ds).mem := by
                    simp [restoreBlockState, hlookup]
            _ = (after.removeVar x).mem := ih (after := after.removeVar x)
            _ = after.mem := by simp
      | some v =>
          calc
            (restoreBlockState before after ((x, ty) :: ds)).mem
                = (restoreBlockState before (after.updateVar x v) ds).mem := by
                    simp [restoreBlockState, hlookup]
            _ = (after.updateVar x v).mem := ih (after := after.updateVar x v)
            _ = after.mem := by simp

@[simp] theorem restoreBlockState_allocs
    (before after : CState) (decls : List (String × CType)) :
    (restoreBlockState before after decls).allocs = after.allocs := by
  induction decls generalizing after with
  | nil =>
      simp [restoreBlockState]
  | cons d ds ih =>
      rcases d with ⟨x, ty⟩
      cases hlookup : before.lookupVar x with
      | none =>
          calc
            (restoreBlockState before after ((x, ty) :: ds)).allocs
                = (restoreBlockState before (after.removeVar x) ds).allocs := by
                    simp [restoreBlockState, hlookup]
            _ = (after.removeVar x).allocs := ih (after := after.removeVar x)
            _ = after.allocs := by simp
      | some v =>
          calc
            (restoreBlockState before after ((x, ty) :: ds)).allocs
                = (restoreBlockState before (after.updateVar x v) ds).allocs := by
                    simp [restoreBlockState, hlookup]
            _ = (after.updateVar x v).allocs := ih (after := after.updateVar x v)
            _ = after.allocs := by simp

theorem lookupVar_enterBlockState_ne (st : CState) (decls : List (String × CType)) (x : String)
    (hnot : ∀ ty, (x, ty) ∉ decls) :
    (enterBlockState st decls).lookupVar x = st.lookupVar x := by
  induction decls generalizing st with
  | nil =>
      simp [enterBlockState]
  | cons d ds ih =>
      rcases d with ⟨y, ty⟩
      have hxy : x ≠ y := by
        intro h
        exact hnot ty (by simp [h])
      have hnotTail : ∀ ty', (x, ty') ∉ ds := by
        intro ty' hmem
        exact hnot ty' (by simp [hmem])
      calc
        (enterBlockState st ((y, ty) :: ds)).lookupVar x
            = (enterBlockState (st.updateVar y CVal.undef) ds).lookupVar x := by
                simp [enterBlockState]
        _ = (st.updateVar y CVal.undef).lookupVar x := by
                exact ih (st := st.updateVar y CVal.undef) hnotTail
        _ = st.lookupVar x := by
                exact lookupVar_updateVar_ne st y x CVal.undef hxy

theorem lookupVar_enterBlockState_of_lookup_undef
    (st : CState) (decls : List (String × CType)) (x : String)
    (hlookup : st.lookupVar x = some CVal.undef) :
    (enterBlockState st decls).lookupVar x = some CVal.undef := by
  induction decls generalizing st with
  | nil =>
      simpa [enterBlockState] using hlookup
  | cons d ds ih =>
      rcases d with ⟨y, ty⟩
      by_cases hxy : x = y
      · subst hxy
        have hlookup' : (st.updateVar x CVal.undef).lookupVar x = some CVal.undef := by
          simpa using lookupVar_updateVar_eq st x CVal.undef
        simpa [enterBlockState] using ih (st := st.updateVar x CVal.undef) hlookup'
      · have hlookup' : (st.updateVar y CVal.undef).lookupVar x = some CVal.undef := by
          rw [lookupVar_updateVar_ne st y x CVal.undef hxy]
          exact hlookup
        simpa [enterBlockState] using ih (st := st.updateVar y CVal.undef) hlookup'

theorem lookupVar_enterBlockState_mem
    (st : CState) (decls : List (String × CType)) (x : String) (ty : CType)
    (hmem : (x, ty) ∈ decls) :
    (enterBlockState st decls).lookupVar x = some CVal.undef := by
  induction decls generalizing st with
  | nil =>
      cases hmem
  | cons d ds ih =>
      rcases d with ⟨y, ty0⟩
      by_cases hxy : x = y
      · subst hxy
        have hlookup : (st.updateVar x CVal.undef).lookupVar x = some CVal.undef := by
          simpa using lookupVar_updateVar_eq st x CVal.undef
        simpa [enterBlockState] using
          lookupVar_enterBlockState_of_lookup_undef
            (st := st.updateVar x CVal.undef) (decls := ds) (x := x) hlookup
      · have hmemTail : (x, ty) ∈ ds := by
          simpa [hxy] using hmem
        calc
          (enterBlockState st ((y, ty0) :: ds)).lookupVar x
              = (enterBlockState (st.updateVar y CVal.undef) ds).lookupVar x := by
                  simp [enterBlockState]
          _ = some CVal.undef := by
                exact ih (st := st.updateVar y CVal.undef) hmemTail

end HeytingLean.LeanCP
