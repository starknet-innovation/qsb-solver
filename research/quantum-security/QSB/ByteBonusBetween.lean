import QSB.FinalBonusBoundary

/-!
The exact four-opcode bridge between the two final-round bonus rolls.
It transports arbitrary shallow byte cells through the fixed deep roll and
the second index's cap. No assumption is made about the selected bytes.
-/
namespace QSB.ByteBonusBetween
open ByteMachine
open FirstAcceptedOrigin
open ByteFinalCounts
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def betweenOps : List Op := ByteLayout.program.drop 845 |>.take 4

theorem generated_between_ops : betweenOps =
    [.push [0x43, 0x02], .roll, .push [0x98, 0x00], .min] := by decide

theorem between_roll_index_decode :
    ByteIndex.parseScriptNum [0x43, 0x02] = some 579 := by decide

theorem successful_cap_min_tail (hashes : Hashes)
    (raw : Bytes) (tail : List Bytes) (outcomes : List Bool)
    (cost : Nat) (next : State)
    (success : step hashes .min
      (State.mk ([0x98, 0x00] :: raw :: tail) outcomes cost) = some next) :
    ∃ retained, next.stack = retained :: tail := by
  unfold step at success
  by_cases budget : cost + 1 > 201
  · simp [budget] at success
  · simp [budget, ByteIndex.positive_152] at success
    cases parsed : ByteIndex.parseScriptNum raw with
    | none => simp [parsed] at success
    | some value =>
        simp [parsed] at success
        cases encoded : ByteIndex.encodeScriptNum (min 152 value) with
        | none => simp [encoded] at success
        | some retained =>
            simp [encoded] at success
            cases success
            exact ⟨retained, rfl⟩

/-- The cap consumes the old top index and leaves every cell below it
unchanged. This holds for any successfully parsed old index. -/
theorem accepted_cap_min_preserves_tail (hashes : Hashes)
    (raw : Bytes) (tail : List Bytes) (outcomes : List Bool)
    (cost : Nat) (final : State) (p : Nat)
    (accepted : run hashes [.push [0x98, 0x00], .min]
      (State.mk (raw :: tail) outcomes cost) = some final) :
    final.stack[p + 1]? = tail[p]? := by
  obtain ⟨afterPush, pushed, _, afterMin⟩ :=
    run_cons_success hashes (.push [0x98, 0x00]) [.min]
      (State.mk (raw :: tail) outcomes cost) final accepted
  have pushShape := push_success_shape hashes [0x98, 0x00]
    (raw :: tail) outcomes cost afterPush pushed
  subst afterPush
  obtain ⟨afterStep, minStep, _, finished⟩ :=
    run_cons_success hashes .min []
      (State.mk ([0x98, 0x00] :: raw :: tail) outcomes cost)
      final afterMin
  obtain ⟨retained, shape⟩ :=
    successful_cap_min_tail hashes raw tail outcomes cost afterStep minStep
  simp [run] at finished
  cases finished
  rw [shape]
  simp

/-- The fixed roll shifts each shallow pre-first-bonus cell one place down;
the second cap preserves that tail. -/
theorem accepted_between_preserves_shallow (hashes : Hashes)
    (stack : List Bytes) (outcomes : List Bool) (cost : Nat)
    (beforeLast : State) (p : Nat) (hp : p < 579)
    (accepted : run hashes betweenOps
      (State.mk stack outcomes cost) = some beforeLast) :
    beforeLast.stack[p + 1]? = stack[p]? := by
  rw [generated_between_ops] at accepted
  have split : ([.push [0x43, 0x02], .roll,
      .push [0x98, 0x00], .min] : List Op) =
      [.push [0x43, 0x02], .roll] ++
      [.push [0x98, 0x00], .min] := rfl
  rw [split, run_append] at accepted
  cases first : run hashes [.push [0x43, 0x02], .roll]
      (State.mk stack outcomes cost) with
  | none => simp [first] at accepted
  | some middle =>
      have moved := accepted_pair_preserves_shallower_option hashes
        [0x43, 0x02] 579 p stack outcomes cost middle
        between_roll_index_decode hp first
      simp only [first, Option.bind_some] at accepted
      cases middle with
      | mk midStack midOutcomes midCost =>
          cases midStack with
          | nil =>
              obtain ⟨afterPush, pushed, _, afterMin⟩ :=
                run_cons_success hashes (.push [0x98, 0x00]) [.min]
                  (State.mk [] midOutcomes midCost) beforeLast accepted
              have pushShape := push_success_shape hashes [0x98, 0x00]
                [] midOutcomes midCost afterPush pushed
              subst afterPush
              obtain ⟨next, minStep, _, _⟩ :=
                run_cons_success hashes .min []
                  (State.mk [[0x98, 0x00]] midOutcomes midCost)
                  beforeLast afterMin
              change (if midCost + 1 > 201 then none else none) =
                some next at minStep
              simp at minStep
          | cons raw tail =>
              have kept := accepted_cap_min_preserves_tail hashes raw tail
                midOutcomes midCost beforeLast p accepted
              change tail[p]? = stack[p]? at moved
              exact kept.trans moved

theorem shallow_first_roll_ninth_source {α : Type*}
    (region rolled : List α) (n : Nat) (hn : n < 9)
    (run : KeyRolls.rollAt n region = some rolled) :
    rolled[9]? = region[9]? := by
  unfold KeyRolls.rollAt at run
  cases hget : region[n]? with
  | none => simp [hget] at run
  | some chosen =>
      simp [hget] at run
      cases run
      simpa using
        (List.getElem?_eraseIdx_of_ge (l := region) (i := n) (j := 8)
          (by omega))

theorem modeled_shallow_first_ninth_source (hashes : Hashes)
    (raw : Bytes) (region : List Bytes) (n : Nat)
    (outcomes : List Bool) (cost : Nat) (postFirst : State)
    (hn : n < 9)
    (decoded : ByteIndex.parseScriptNum raw = some (Int.ofNat n))
    (roll : run hashes [.roll]
      (State.mk (raw :: region) outcomes cost) = some postFirst) :
    postFirst.stack[9]? = region[9]? := by
  obtain ⟨afterRoll, rolled, _, finished⟩ :=
    run_cons_success hashes .roll []
      (State.mk (raw :: region) outcomes cost) postFirst roll
  have budget := roll_success_budget hashes raw region outcomes cost
    afterRoll rolled
  rw [FirstOvershoot.byte_roll_matches_list_roll hashes raw n region
    outcomes cost decoded budget] at rolled
  cases hroll : KeyRolls.rollAt n region with
  | none => simp [hroll] at rolled
  | some rolledStack =>
      have source := shallow_first_roll_ninth_source region rolledStack
        n hn hroll
      simp [hroll] at rolled
      cases rolled
      simp [run] at finished
      cases finished
      exact source

/-- If both first-bonus source cells at depths nine and ten are nonempty,
then a shallow first bonus choice makes success impossible, regardless of
the last bonus choice and the supplied signature outcomes. -/
theorem successful_two_bonus_requires_first_depth_nine (hashes : Hashes)
    (rawFirst rawLast : Bytes) (regionFirst regionLast : List Bytes)
    (firstIndex lastIndex : Nat) (outcomes : List Bool) (cost : Nat)
    (postFirst beforeLast postLast final : State)
    (nine ten : Bytes) (nineNonempty : nine ≠ []) (tenNonempty : ten ≠ [])
    (firstNine : regionFirst[9]? = some nine)
    (firstTen : regionFirst[10]? = some ten)
    (decodedFirst : ByteIndex.parseScriptNum rawFirst =
      some (Int.ofNat firstIndex))
    (decodedLast : ByteIndex.parseScriptNum rawLast =
      some (Int.ofNat lastIndex))
    (firstRoll : run hashes [.roll]
      (State.mk (rawFirst :: regionFirst) outcomes cost) = some postFirst)
    (between : run hashes betweenOps postFirst = some beforeLast)
    (lastShape : beforeLast.stack = rawLast :: regionLast)
    (lastRoll : run hashes [.roll] beforeLast = some postLast)
    (suffix : run hashes (ByteLayout.program.drop 850)
      postLast = some final) :
    9 ≤ firstIndex := by
  by_contra tooSmall
  have shallow : firstIndex < 9 := by omega
  have firstNineMoved := modeled_shallow_first_ninth_source hashes
    rawFirst regionFirst firstIndex outcomes cost postFirst shallow
    decodedFirst firstRoll
  have firstTenMoved := FinalBonusBoundary.modeled_shallow_bonus_tenth_source
    hashes rawFirst regionFirst firstIndex outcomes cost postFirst
    (by omega) decodedFirst firstRoll
  cases postFirst with
  | mk firstStack firstOutcomes firstCost =>
      have betweenNine := accepted_between_preserves_shallow hashes
        firstStack firstOutcomes firstCost beforeLast 9 (by omega) between
      have betweenTen := accepted_between_preserves_shallow hashes
        firstStack firstOutcomes firstCost beforeLast 10 (by omega) between
      have lastNine : regionLast[9]? = some nine := by
        rw [lastShape] at betweenNine
        simpa using betweenNine.trans (firstNineMoved.trans firstNine)
      have lastTen : regionLast[10]? = some ten := by
        rw [lastShape] at betweenTen
        simpa using betweenTen.trans (firstTenMoved.trans firstTen)
      cases beforeLast with
      | mk lastStack lastOutcomes lastCost =>
          change lastStack = rawLast :: regionLast at lastShape
          subst lastStack
          exact FinalBonusBoundary.two_nonempty_dummy_sources_reject
            hashes rawLast regionLast lastIndex lastOutcomes lastCost
            postLast final nine ten nineNonempty tenNonempty lastNine
            lastTen decodedLast lastRoll suffix

/-- Once both pre-first-bonus candidate pool cells are nonempty, successful
modeled execution imposes both boundary indices. The last-index bound follows
because the first roll leaves one of those two cells at post-first depth ten,
which the fixed roll and cap carry to last-roll source depth ten. -/
theorem successful_two_bonus_index_bounds (hashes : Hashes)
    (rawFirst rawLast : Bytes) (regionFirst regionLast : List Bytes)
    (firstIndex lastIndex : Nat) (outcomes : List Bool) (cost : Nat)
    (postFirst beforeLast postLast final : State)
    (nine ten : Bytes) (nineNonempty : nine ≠ []) (tenNonempty : ten ≠ [])
    (firstNine : regionFirst[9]? = some nine)
    (firstTen : regionFirst[10]? = some ten)
    (decodedFirst : ByteIndex.parseScriptNum rawFirst =
      some (Int.ofNat firstIndex))
    (decodedLast : ByteIndex.parseScriptNum rawLast =
      some (Int.ofNat lastIndex))
    (firstRoll : run hashes [.roll]
      (State.mk (rawFirst :: regionFirst) outcomes cost) = some postFirst)
    (between : run hashes betweenOps postFirst = some beforeLast)
    (lastShape : beforeLast.stack = rawLast :: regionLast)
    (lastRoll : run hashes [.roll] beforeLast = some postLast)
    (suffix : run hashes (ByteLayout.program.drop 850)
      postLast = some final) :
    9 ≤ firstIndex ∧ 10 ≤ lastIndex := by
  have firstBound := successful_two_bonus_requires_first_depth_nine
    hashes rawFirst rawLast regionFirst regionLast firstIndex lastIndex
    outcomes cost postFirst beforeLast postLast final nine ten
    nineNonempty tenNonempty firstNine firstTen decodedFirst decodedLast
    firstRoll between lastShape lastRoll suffix
  have firstSource : ∃ marker : Bytes, marker ≠ [] ∧
      postFirst.stack[10]? = some marker := by
    by_cases shallow : firstIndex < 10
    · have source := FinalBonusBoundary.modeled_shallow_bonus_tenth_source
        hashes rawFirst regionFirst firstIndex outcomes cost postFirst
        shallow decodedFirst firstRoll
      exact ⟨ten, tenNonempty, source.trans firstTen⟩
    · have deep : 10 ≤ firstIndex := by omega
      have source := FinalBonusBoundary.modeled_deep_bonus_tenth_source
        hashes rawFirst regionFirst firstIndex outcomes cost postFirst
        deep decodedFirst firstRoll
      exact ⟨nine, nineNonempty, source.trans firstNine⟩
  obtain ⟨marker, nonempty, postTen⟩ := firstSource
  cases postFirst with
  | mk firstStack firstOutcomes firstCost =>
      have carried := accepted_between_preserves_shallow hashes
        firstStack firstOutcomes firstCost beforeLast 10 (by omega) between
      have lastTen : regionLast[10]? = some marker := by
        rw [lastShape] at carried
        simpa using carried.trans postTen
      cases beforeLast with
      | mk lastStack lastOutcomes lastCost =>
          change lastStack = rawLast :: regionLast at lastShape
          subst lastStack
          have lastBound :=
            FinalBonusBoundary.successful_bonus_requires_depth_at_least_ten
              hashes rawLast regionLast lastIndex lastOutcomes lastCost
              postLast final marker nonempty lastTen decodedLast
              lastRoll suffix
          exact ⟨firstBound, lastBound⟩

end QSB.ByteBonusBetween
