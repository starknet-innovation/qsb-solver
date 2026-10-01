import QSB.BytePrefixCapacity

/-!
A successful modeled opcode cannot start reading new cells merely because
an extra stack suffix was placed below its already sufficient input stack.
This holds for `OP_ROLL` and `CHECKMULTISIG` as well as the local opcodes.
The full run lifts this frame property when the enlarged stack remains within
the 1000-cell guard. It does not formalize compiled Bitcoin Core or scriptSig.
-/
namespace QSB.ByteStackFrame
open QSB.ByteMachine
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

theorem push_frame (hashes : Hashes) (value : Bytes) (s next : State)
    (tail : List Bytes) (h : step hashes (.push value) s = some next) :
    step hashes (.push value) {s with stack := s.stack ++ tail} =
      some {next with stack := next.stack ++ tail} := by
  unfold step at h ⊢
  simp at h ⊢
  rcases h with ⟨budget, small, rfl⟩
  simp [budget, small]

theorem dup_frame (hashes : Hashes) (s next : State)
    (tail : List Bytes) (h : step hashes .dup s = some next) :
    step hashes .dup {s with stack := s.stack ++ tail} =
      some {next with stack := next.stack ++ tail} := by
  unfold step at h ⊢
  cases hs : s.stack with
  | nil => simp [hs] at h
  | cons x xs =>
      simp [hs] at h ⊢
      rcases h with ⟨budget, rfl⟩
      simp [budget]

theorem over_frame (hashes : Hashes) (s next : State)
    (tail : List Bytes) (h : step hashes .over s = some next) :
    step hashes .over {s with stack := s.stack ++ tail} =
      some {next with stack := next.stack ++ tail} := by
  unfold step at h ⊢
  cases hs : s.stack with
  | nil => simp [hs] at h
  | cons x xs =>
      cases ht : xs with
      | nil => simp [hs, ht] at h
      | cons y rest =>
          simp [hs, ht] at h ⊢
          rcases h with ⟨budget, rfl⟩
          simp [budget]

theorem min_frame (hashes : Hashes) (s next : State)
    (tail : List Bytes) (h : step hashes .min s = some next) :
    step hashes .min {s with stack := s.stack ++ tail} =
      some {next with stack := next.stack ++ tail} := by
  unfold step at h ⊢
  cases hs : s.stack with
  | nil => simp [hs] at h
  | cons x xs =>
      cases ht : xs with
      | nil => simp [hs, ht] at h
      | cons y rest =>
          simp [hs, ht] at h ⊢
          cases hx : QSB.ByteIndex.parseScriptNum x with
          | none => simp [hx] at h
          | some a =>
              cases hy : QSB.ByteIndex.parseScriptNum y with
              | none => simp [hx, hy] at h
              | some b =>
                  cases hv : QSB.ByteIndex.encodeScriptNum (min a b) with
                  | none => simp [hx, hy, hv] at h
                  | some value =>
                      simp [hx, hy, hv] at h ⊢
                      rcases h with ⟨budget, rfl⟩
                      simp [budget]

theorem swap_frame (hashes : Hashes) (s next : State)
    (tail : List Bytes) (h : step hashes .swap s = some next) :
    step hashes .swap {s with stack := s.stack ++ tail} =
      some {next with stack := next.stack ++ tail} := by
  unfold step at h ⊢
  cases hs : s.stack with
  | nil => simp [hs] at h
  | cons x xs =>
      cases ht : xs with
      | nil => simp [hs, ht] at h
      | cons y rest =>
          simp [hs, ht] at h ⊢
          rcases h with ⟨budget, rfl⟩
          simp [budget]

theorem hash160_frame (hashes : Hashes) (s next : State)
    (tail : List Bytes) (h : step hashes .hash160 s = some next) :
    step hashes .hash160 {s with stack := s.stack ++ tail} =
      some {next with stack := next.stack ++ tail} := by
  unfold step at h ⊢
  cases hs : s.stack with
  | nil => simp [hs] at h
  | cons x xs =>
      simp [hs] at h ⊢
      rcases h with ⟨budget, rfl⟩
      simp [budget]

theorem sha256_frame (hashes : Hashes) (s next : State)
    (tail : List Bytes) (h : step hashes .sha256 s = some next) :
    step hashes .sha256 {s with stack := s.stack ++ tail} =
      some {next with stack := next.stack ++ tail} := by
  unfold step at h ⊢
  cases hs : s.stack with
  | nil => simp [hs] at h
  | cons x xs =>
      simp [hs] at h ⊢
      rcases h with ⟨budget, rfl⟩
      simp [budget]

theorem equalverify_frame (hashes : Hashes) (s next : State)
    (tail : List Bytes) (h : step hashes .equalverify s = some next) :
    step hashes .equalverify {s with stack := s.stack ++ tail} =
      some {next with stack := next.stack ++ tail} := by
  unfold step at h ⊢
  cases hs : s.stack with
  | nil => simp [hs] at h
  | cons x xs =>
      cases ht : xs with
      | nil => simp [hs, ht] at h
      | cons y rest =>
          by_cases equal : x = y
          · simp [hs, ht, equal] at h ⊢
            rcases h with ⟨budget, rfl⟩
            simp [budget]
          · simp [hs, ht, equal] at h

theorem checksigverify_frame (hashes : Hashes) (s next : State)
    (tail : List Bytes) (h : step hashes .checksigverify s = some next) :
    step hashes .checksigverify {s with stack := s.stack ++ tail} =
      some {next with stack := next.stack ++ tail} := by
  unfold step at h ⊢
  cases hs : s.stack with
  | nil => simp [hs] at h
  | cons x xs =>
      cases ht : xs with
      | nil => simp [hs, ht] at h
      | cons y rest =>
          cases ho : s.outcomes with
          | nil => simp [hs, ht, ho] at h
          | cons b more =>
              cases b with
              | false => simp [hs, ht, ho] at h
              | true =>
                  simp [hs, ht, ho] at h ⊢
                  rcases h with ⟨budget, rfl⟩
                  simp [budget]

theorem add_frame (hashes : Hashes) (s next : State)
    (tail : List Bytes) (h : step hashes .add s = some next) :
    step hashes .add {s with stack := s.stack ++ tail} =
      some {next with stack := next.stack ++ tail} := by
  unfold step at h ⊢
  cases hs : s.stack with
  | nil => simp [hs] at h
  | cons x xs =>
      cases ht : xs with
      | nil => simp [hs, ht] at h
      | cons y rest =>
          simp [hs, ht] at h ⊢
          cases hx : QSB.ByteIndex.parseScriptNum x with
          | none => simp [hx] at h
          | some a =>
              cases hy : QSB.ByteIndex.parseScriptNum y with
              | none => simp [hx, hy] at h
              | some b =>
                  cases hv : QSB.ByteIndex.encodeScriptNum (a + b) with
                  | none => simp [hx, hy, hv] at h
                  | some value =>
                      simp [hx, hy, hv] at h ⊢
                      rcases h with ⟨budget, rfl⟩
                      simp [budget]

theorem roll_frame (hashes : Hashes) (s next : State)
    (tail : List Bytes) (h : step hashes .roll s = some next) :
    step hashes .roll {s with stack := s.stack ++ tail} =
      some {next with stack := next.stack ++ tail} := by
  unfold step at h ⊢
  cases hs : s.stack with
  | nil => simp [hs] at h
  | cons raw xs =>
      simp [hs] at h ⊢
      cases hp : QSB.ByteIndex.parseScriptNum raw with
      | none => simp [hp] at h
      | some n =>
          by_cases negative : n < 0
          · simp [hp, negative] at h
          · cases hg : xs[n.toNat]? with
            | none => simp [hp, negative, hg] at h
            | some x =>
                have bound : n.toNat < xs.length :=
                  (List.getElem?_eq_some_iff.mp hg).choose
                have getAppend := List.getElem?_append_left
                  (l₁ := xs) (l₂ := tail) bound
                have eraseAppend := List.eraseIdx_append_of_lt_length
                  (l := xs) bound tail
                simp [hp, negative, hg, getAppend, eraseAppend] at h ⊢
                rcases h with ⟨budget, rfl⟩
                simp [budget]

theorem checkmultisig_frame (hashes : Hashes) (s next : State)
    (tail : List Bytes) (h : step hashes .checkmultisig s = some next) :
    step hashes .checkmultisig {s with stack := s.stack ++ tail} =
      some {next with stack := next.stack ++ tail} := by
  unfold step at h ⊢
  cases hs : s.stack with
  | nil => simp [hs] at h
  | cons rawN xs =>
      simp [hs] at h ⊢
      cases hn : QSB.ByteIndex.parseScriptNum rawN with
      | none => simp [hn] at h
      | some n =>
          by_cases badN : n < 0 ∨ 20 < n ∨ 201 < s.ops + 1 + n.toNat
          · simp [hn, badN] at h
          · cases hraw : xs[n.toNat]? with
            | none => simp [hn, badN, hraw] at h
            | some rawM =>
                have nBound : n.toNat < xs.length :=
                  (List.getElem?_eq_some_iff.mp hraw).choose
                have nAppend := List.getElem?_append_left
                  (l₁ := xs) (l₂ := tail) nBound
                simp [hn, badN, hraw, nAppend] at h ⊢
                cases hm : QSB.ByteIndex.parseScriptNum rawM with
                | none => simp [hm] at h
                | some m =>
                    by_cases badM : m < 0 ∨ n < m
                    · simp [hm, badM] at h
                    · cases hdummy : xs[n.toNat + 1 + m.toNat]? with
                      | none => simp [hm, badM, hdummy] at h
                      | some dummy =>
                          have dummyBound :
                              n.toNat + 1 + m.toNat < xs.length :=
                            (List.getElem?_eq_some_iff.mp hdummy).choose
                          have dummyAppend := List.getElem?_append_left
                            (l₁ := xs) (l₂ := tail) dummyBound
                          simp [hm, badM, hdummy, dummyAppend] at h ⊢
                          have dropBound :
                              n.toNat + m.toNat + 2 ≤ xs.length := by
                            omega
                          have dropAppend := List.drop_append_of_le_length
                            (l₁ := xs) (l₂ := tail) dropBound
                          cases ho : s.outcomes with
                          | nil => simp [ho] at h
                          | cons b rest =>
                              simp [ho, dropAppend] at h ⊢
                              rcases h with ⟨budget, empty, rfl⟩
                              simp [budget, empty]

theorem step_frame (hashes : Hashes) (op : Op) (s next : State)
    (tail : List Bytes) (h : step hashes op s = some next) :
    step hashes op {s with stack := s.stack ++ tail} =
      some {next with stack := next.stack ++ tail} := by
  cases op with
  | push value => exact push_frame hashes value s next tail h
  | dup => exact dup_frame hashes s next tail h
  | over => exact over_frame hashes s next tail h
  | swap => exact swap_frame hashes s next tail h
  | roll => exact roll_frame hashes s next tail h
  | min => exact min_frame hashes s next tail h
  | add => exact add_frame hashes s next tail h
  | hash160 => exact hash160_frame hashes s next tail h
  | sha256 => exact sha256_frame hashes s next tail h
  | equalverify => exact equalverify_frame hashes s next tail h
  | checksigverify => exact checksigverify_frame hashes s next tail h
  | checkmultisig => exact checkmultisig_frame hashes s next tail h

theorem runPeak_frame (hashes : Hashes) (ops : List Op)
    (s final : State) (peak : Nat) (tail : List Bytes)
    (base : QSB.BytePrefixCapacity.runPeak hashes ops s = some (final, peak))
    (capacity : peak + tail.length ≤ 1000) :
    QSB.BytePrefixCapacity.runPeak hashes ops
      {s with stack := s.stack ++ tail} =
      some ({final with stack := final.stack ++ tail},
        peak + tail.length) := by
  induction ops generalizing s final peak with
  | nil =>
      simp [QSB.BytePrefixCapacity.runPeak] at base ⊢
      rcases base with ⟨rfl, rfl⟩
      simp
  | cons op rest ih =>
      simp only [QSB.BytePrefixCapacity.runPeak] at base ⊢
      cases hstep : step hashes op s with
      | none => simp [hstep] at base
      | some next =>
          by_cases large : next.stack.length > 1000
          · simp [hstep, large] at base
          · cases htail : QSB.BytePrefixCapacity.runPeak hashes rest next with
            | none => simp [hstep, large, htail] at base
            | some value =>
                rcases value with ⟨reached, laterPeak⟩
                simp [hstep, large, htail] at base
                rcases base with ⟨rfl, rfl⟩
                have nextCapacity : next.stack.length + tail.length ≤ 1000 := by
                  have bound := Nat.le_max_left next.stack.length laterPeak
                  omega
                have tailCapacity : laterPeak + tail.length ≤ 1000 := by
                  have bound := Nat.le_max_right next.stack.length laterPeak
                  omega
                have framedStep := step_frame hashes op s next tail hstep
                have framedTail := ih next reached laterPeak htail tailCapacity
                simp [framedStep, nextCapacity, framedTail,
                  List.length_append]

/-- For a nonempty successful base run, an appended lower stack suffix that
pushes the base peak beyond the post-op 1000-cell guard must fail. The guard
is not checked for an empty program, hence the nonempty premise. -/
theorem runPeak_frame_overflow (hashes : Hashes) (ops : List Op)
    (s final : State) (peak : Nat) (tail : List Bytes)
    (nonempty : ops ≠ [])
    (base : QSB.BytePrefixCapacity.runPeak hashes ops s = some (final, peak))
    (overflow : peak + tail.length > 1000) :
    QSB.BytePrefixCapacity.runPeak hashes ops
      {s with stack := s.stack ++ tail} = none := by
  induction ops generalizing s final peak with
  | nil => contradiction
  | cons op rest ih =>
      simp only [QSB.BytePrefixCapacity.runPeak] at base ⊢
      cases hstep : step hashes op s with
      | none => simp [hstep] at base
      | some next =>
          by_cases large : next.stack.length > 1000
          · simp [hstep, large] at base
          · cases htail : QSB.BytePrefixCapacity.runPeak hashes rest next with
            | none => simp [hstep, large, htail] at base
            | some value =>
                rcases value with ⟨reached, laterPeak⟩
                simp [hstep, large, htail] at base
                rcases base with ⟨rfl, rfl⟩
                have framedStep := step_frame hashes op s next tail hstep
                by_cases immediate : next.stack.length + tail.length > 1000
                · simp [framedStep, List.length_append, immediate]
                · have lateOver : laterPeak + tail.length > 1000 := by
                    omega
                  by_cases restEmpty : rest = []
                  · subst rest
                    simp [QSB.BytePrefixCapacity.runPeak] at htail
                    rcases htail with ⟨rfl, rfl⟩
                    omega
                  · have failed := ih next reached laterPeak restEmpty
                        htail lateOver
                    simp [framedStep, List.length_append, immediate, failed]

theorem finalTruth_frame (s : State) (tail : List Bytes)
    (truth : finalTruth s = true) :
    finalTruth {s with stack := s.stack ++ tail} = true := by
  cases hs : s.stack with
  | nil => simp [finalTruth, hs] at truth
  | cons x rest => simpa [finalTruth, hs] using truth

/-- Any bottom-stack byte values, including empty and nonempty cells, leave
this disposable canonical witness's modeled result unchanged when at most
385 cells are added. The exact peak and final stack height increase by the
number of added cells. This is an instance of the general frame theorem,
not 386 separate evaluations or a Core acceptance theorem. -/
theorem canonical_arbitrary_bottom_tail
    (tail : List Bytes) (within : tail.length ≤ 385) :
    (QSB.BytePrefixCapacity.runPeak QSB.ByteWitness.hashes
      QSB.ByteLayout.program
      ⟨QSB.ByteWitness.witness ++ tail,
        [true, true, true, false, true, true], 0⟩).map
        (fun result => (finalTruth result.1, result.2,
          result.1.stack.length)) =
      some (true, 615 + tail.length, 569 + tail.length) := by
  have base := QSB.BytePrefixCapacity.canonical_peak
  cases hrun : QSB.BytePrefixCapacity.runPeak QSB.ByteWitness.hashes
      QSB.ByteLayout.program (QSB.BytePrefixCapacity.input 0) with
  | none => simp [hrun] at base
  | some value =>
      rcases value with ⟨final, peak⟩
      simp [hrun] at base
      rcases base with ⟨truth, peakEq, lengthEq⟩
      have capacity : peak + tail.length ≤ 1000 := by omega
      have framed := runPeak_frame QSB.ByteWitness.hashes
        QSB.ByteLayout.program (QSB.BytePrefixCapacity.input 0)
        final peak tail hrun capacity
      have framedTruth := finalTruth_frame final tail truth
      simpa [QSB.BytePrefixCapacity.input, framedTruth, peakEq, lengthEq,
        List.length_append] using congrArg
          (Option.map fun result =>
            (finalTruth result.1, result.2, result.1.stack.length)) framed

/-- The same disposable fixture overflows for every lower byte-cell suffix
of length at least 386, independent of cell contents. -/
theorem canonical_arbitrary_bottom_tail_overflow
    (tail : List Bytes) (over : 386 ≤ tail.length) :
    QSB.BytePrefixCapacity.runPeak QSB.ByteWitness.hashes
      QSB.ByteLayout.program
      ⟨QSB.ByteWitness.witness ++ tail,
        [true, true, true, false, true, true], 0⟩ = none := by
  have base := QSB.BytePrefixCapacity.canonical_peak
  cases hrun : QSB.BytePrefixCapacity.runPeak QSB.ByteWitness.hashes
      QSB.ByteLayout.program (QSB.BytePrefixCapacity.input 0) with
  | none => simp [hrun] at base
  | some value =>
      rcases value with ⟨final, peak⟩
      simp [hrun] at base
      rcases base with ⟨_truth, peakEq, _lengthEq⟩
      have overflow : peak + tail.length > 1000 := by omega
      have failed := runPeak_frame_overflow QSB.ByteWitness.hashes
        QSB.ByteLayout.program (QSB.BytePrefixCapacity.input 0)
        final peak tail (by decide) hrun overflow
      simpa [QSB.BytePrefixCapacity.input] using failed

theorem canonical_arbitrary_bottom_tail_byte_run_rejects
    (tail : List Bytes) (over : 386 ≤ tail.length) :
    ByteMachine.run QSB.ByteWitness.hashes QSB.ByteLayout.program
      ⟨QSB.ByteWitness.witness ++ tail,
        [true, true, true, false, true, true], 0⟩ = none := by
  have erase := QSB.BytePrefixCapacity.forget_peak QSB.ByteWitness.hashes
    QSB.ByteLayout.program
    (⟨QSB.ByteWitness.witness ++ tail,
      [true, true, true, false, true, true], 0⟩ : State)
  simpa [canonical_arbitrary_bottom_tail_overflow tail over] using erase.symm

end QSB.ByteStackFrame
