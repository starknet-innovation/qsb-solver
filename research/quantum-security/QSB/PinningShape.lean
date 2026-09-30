import QSB.FirstAcceptedOrigin

/-!
The byte-model pinning prefix is analyzed without assuming an initial stack
shape or signature outcomes. This still leaves scriptSig execution and the
meaning of Boolean CHECKSIGVERIFY outcomes outside the model.
-/
namespace QSB.PinningShape
open ByteMachine
open FirstOvershoot
open FirstAcceptedOrigin
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

theorem accepted_has_pinning_prefix (hashes : Hashes)
    (stack : List Bytes) (outcomes : List Bool) (final : State)
    (accepted : run hashes ByteLayout.program
      (State.mk stack outcomes 0) = some final) :
    ∃ middle,
      run hashes (ByteLayout.program.take 6)
        (State.mk stack outcomes 0) = some middle := by
  rw [generated_program_split_pinning] at accepted
  exact successful_prefix hashes (ByteLayout.program.take 6)
    (ByteLayout.program.drop 6) (State.mk stack outcomes 0)
    final accepted

theorem accepted_pinning_input_shape (hashes : Hashes)
    (stack : List Bytes) (outcomes : List Bool) (final : State)
    (accepted : run hashes ByteLayout.program
      (State.mk stack outcomes 0) = some final) :
    ∃ nonce puzzle tail later,
      stack = nonce :: puzzle :: tail ∧
      outcomes = true :: true :: later := by
  obtain ⟨middle, pinning⟩ :=
    accepted_has_pinning_prefix hashes stack outcomes final accepted
  rw [generated_pinning_opcodes] at pinning
  obtain ⟨afterPush, pushStep, _pushSize, remainingPush⟩ :=
    run_cons_success hashes (.push pinSignature)
      [.over, .checksigverify, .sha256, .swap, .checksigverify]
      (State.mk stack outcomes 0) middle pinning
  have pushExact : step hashes (.push pinSignature)
      (State.mk stack outcomes 0) =
      some (State.mk (pinSignature :: stack) outcomes 0) := by
    unfold step
    have fits : ¬ pinSignature.length > 520 :=
      Nat.not_lt.mpr pin_signature_fits
    simp [fits]
  have pushState : afterPush =
      State.mk (pinSignature :: stack) outcomes 0 := by
    rw [pushExact] at pushStep
    simpa using pushStep.symm
  subst afterPush
  obtain ⟨afterOver, overStep, _overSize, remainingOver⟩ :=
    run_cons_success hashes .over
      [.checksigverify, .sha256, .swap, .checksigverify]
      (State.mk (pinSignature :: stack) outcomes 0) middle remainingPush
  cases stack with
  | nil =>
      unfold step at overStep
      simp at overStep
  | cons nonce rest =>
      have overExact : step hashes .over
          (State.mk (pinSignature :: nonce :: rest) outcomes 0) =
          some (State.mk (nonce :: pinSignature :: nonce :: rest)
            outcomes 1) := by
        unfold step
        simp
      have overState : afterOver =
          State.mk (nonce :: pinSignature :: nonce :: rest)
            outcomes 1 := by
        rw [overExact] at overStep
        simpa using overStep.symm
      subst afterOver
      obtain ⟨afterFirstCheck, firstCheck, _checkSize, remainingCheck⟩ :=
        run_cons_success hashes .checksigverify
          [.sha256, .swap, .checksigverify]
          (State.mk (nonce :: pinSignature :: nonce :: rest)
            outcomes 1) middle remainingOver
      cases outcomes with
      | nil =>
          unfold step at firstCheck
          simp at firstCheck
      | cons first later =>
          cases first with
          | false =>
              unfold step at firstCheck
              simp at firstCheck
          | true =>
              have firstExact : step hashes .checksigverify
                  (State.mk (nonce :: pinSignature :: nonce :: rest)
                    (true :: later) 1) =
                  some (State.mk (nonce :: rest) later 2) := by
                unfold step
                simp
              have firstState : afterFirstCheck =
                  State.mk (nonce :: rest) later 2 := by
                rw [firstExact] at firstCheck
                simpa using firstCheck.symm
              subst afterFirstCheck
              obtain ⟨afterHash, hashStep, _hashSize, remainingHash⟩ :=
                run_cons_success hashes .sha256
                  [.swap, .checksigverify]
                  (State.mk (nonce :: rest) later 2) middle remainingCheck
              have hashExact : step hashes .sha256
                  (State.mk (nonce :: rest) later 2) =
                  some (State.mk (hashes.h256 nonce :: rest) later 3) := by
                unfold step
                simp
              have hashState : afterHash =
                  State.mk (hashes.h256 nonce :: rest) later 3 := by
                rw [hashExact] at hashStep
                simpa using hashStep.symm
              subst afterHash
              obtain ⟨afterSwap, swapStep, _swapSize, remainingSwap⟩ :=
                run_cons_success hashes .swap [.checksigverify]
                  (State.mk (hashes.h256 nonce :: rest) later 3)
                  middle remainingHash
              cases rest with
              | nil =>
                  unfold step at swapStep
                  simp at swapStep
              | cons puzzle tail =>
                  have swapExact : step hashes .swap
                      (State.mk (hashes.h256 nonce :: puzzle :: tail)
                        later 3) =
                      some (State.mk (puzzle :: hashes.h256 nonce :: tail)
                        later 4) := by
                    unfold step
                    simp
                  have swapState : afterSwap =
                      State.mk (puzzle :: hashes.h256 nonce :: tail)
                        later 4 := by
                    rw [swapExact] at swapStep
                    simpa using swapStep.symm
                  subst afterSwap
                  obtain ⟨afterSecondCheck, secondCheck,
                      _secondSize, _remainingSecond⟩ :=
                    run_cons_success hashes .checksigverify []
                      (State.mk (puzzle :: hashes.h256 nonce :: tail)
                        later 4) middle remainingSwap
                  cases later with
                  | nil =>
                      unfold step at secondCheck
                      simp at secondCheck
                  | cons second remaining =>
                      cases second with
                      | false =>
                          unfold step at secondCheck
                          simp at secondCheck
                      | true =>
                          exact ⟨nonce, puzzle, tail, remaining, rfl, rfl⟩

theorem empty_post_pinning_first_roll_fails (hashes : Hashes)
    (outcomes : List Bool) :
    run hashes [.push [0x2e, 0x01], .roll]
      (State.mk (fixedRegion ++ []) outcomes 5) = none := by
  have firstPush : step hashes (.push [0x2e, 0x01])
      (State.mk (fixedRegion ++ []) outcomes 5) =
      some (State.mk ([0x2e, 0x01] :: (fixedRegion ++ [])) outcomes 5) := by
    unfold step
    simp
  unfold run
  rw [firstPush]
  change (Option.bind
    (some (State.mk ([0x2e, 0x01] :: (fixedRegion ++ [])) outcomes 5))
    (fun s' => if s'.stack.length > 1000 then none
      else run hashes [.roll] s')) = none
  simp only [Option.bind_some]
  have fits : ¬ ([0x2e, 0x01] :: (fixedRegion ++ [])).length > 1000 := by
    rw [List.length_cons, List.length_append, fixed_region_length]
    simp only [List.length_nil]
    omega
  rw [if_neg fits]
  unfold run
  rw [byte_roll_matches_list_roll hashes [0x2e, 0x01] 302
    (fixedRegion ++ []) outcomes 5 (by decide) (by omega)]
  have missing : fixedRegion[302]? = none := by
    apply List.getElem?_eq_none
    rw [fixed_region_length]
  simp [KeyRolls.rollAt, missing]

theorem two_cell_initial_stack_cannot_accept (hashes : Hashes)
    (nonce puzzle : Bytes) (later : List Bool) (final : State)
    (accepted : run hashes ByteLayout.program
      (State.mk [nonce, puzzle] (true :: true :: later) 0) = some final) :
    False := by
  have pinning := modeled_pinning_consumes_two_keys hashes
    nonce puzzle ([] : List Bytes) later (by simp)
  have prefixState := generated_prefix_after_pinning hashes
    (State.mk [nonce, puzzle] (true :: true :: later) 0)
    [] later pinning (by simp)
  have firstTwo : (ByteLayout.program.drop 308).take 2 =
      [.push [0x2e, 0x01], .roll] := by decide
  have prefix310Split : ByteLayout.program.take 310 =
      ByteLayout.program.take 308 ++
        (ByteLayout.program.drop 308).take 2 := by decide
  have programSplit : ByteLayout.program =
      ByteLayout.program.take 310 ++ ByteLayout.program.drop 310 := by decide
  rw [programSplit] at accepted
  obtain ⟨middle, first310Success⟩ :=
    successful_prefix hashes (ByteLayout.program.take 310)
      (ByteLayout.program.drop 310)
      (State.mk [nonce, puzzle] (true :: true :: later) 0)
      final accepted
  have first310Fails : run hashes (ByteLayout.program.take 310)
      (State.mk [nonce, puzzle] (true :: true :: later) 0) = none := by
    rw [prefix310Split]
    rw [run_append hashes (ByteLayout.program.take 308)
      ((ByteLayout.program.drop 308).take 2), prefixState]
    simp only [Option.bind_some]
    rw [firstTwo]
    exact empty_post_pinning_first_roll_fails hashes later
  have contradiction : some middle = none :=
    first310Success.symm.trans first310Fails
  cases contradiction

theorem accepted_initial_shape (hashes : Hashes)
    (stack : List Bytes) (outcomes : List Bool) (final : State)
    (accepted : run hashes ByteLayout.program
      (State.mk stack outcomes 0) = some final) :
    ∃ nonce puzzle raw tail later,
      stack = nonce :: puzzle :: raw :: tail ∧
      outcomes = true :: true :: later := by
  obtain ⟨nonce, puzzle, post, later, stackShape, outcomeShape⟩ :=
    accepted_pinning_input_shape hashes stack outcomes final accepted
  subst stack
  subst outcomes
  cases post with
  | nil =>
      exact (two_cell_initial_stack_cannot_accept hashes nonce puzzle
        later final accepted).elim
  | cons raw tail =>
      exact ⟨nonce, puzzle, raw, tail, later, rfl, rfl⟩

/-- Every successful byte-model run from an arbitrary initial byte stack and
arbitrary Boolean outcome list must have its first signed hash comparison
against a fixed lock commitment. This discharges the earlier top-stack and
pinning-outcome premises *inside the byte model*. It does not prove that a
real Bitcoin scriptSig creates this state or justify the Boolean outcomes. -/
theorem accepted_arbitrary_initial_stack_first_origin (hashes : Hashes)
    (stack : List Bytes) (outcomes : List Bool) (final : State)
    (accepted : run hashes ByteLayout.program
      (State.mk stack outcomes 0) = some final) :
    ∃ nonce puzzle raw tail later,
      stack = nonce :: puzzle :: raw :: tail ∧
      outcomes = true :: true :: later ∧
      ∃ i : Fin 150, ∃ opening : Bytes,
        ByteIndex.parseScriptNum raw = some (Int.ofNat (2 + i.val)) ∧
        fixedRegion[152 + i.val]? = some (hashes.h160 opening) := by
  obtain ⟨nonce, puzzle, raw, tail, later, stackShape, outcomeShape⟩ :=
    accepted_initial_shape hashes stack outcomes final accepted
  subst stack
  subst outcomes
  obtain ⟨i, opening, parsed, commitment⟩ :=
    accepted_first_signed_commitment_origin hashes nonce puzzle raw tail
      later final accepted
  exact ⟨nonce, puzzle, raw, tail, later, rfl, rfl,
    i, opening, parsed, commitment⟩

end QSB.PinningShape
