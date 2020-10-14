Inductive bool :=
  | true
  | false.

Parameter prop_variables : Set.

Check prop_variables.

Inductive prop_formula : Set := 
                       | Var : prop_variables -> prop_formula
                       | Top : prop_formula 
                       | Bottom : prop_formula 
                       | Not : prop_formula -> prop_formula
                       | And : prop_formula -> prop_formula -> prop_formula
                       | Or : prop_formula -> prop_formula -> prop_formula.

Notation "⊥" := Bottom.
Notation "⊤" := Top.
Notation "¬ P" := (Not P) (at level 51).
Infix "∧" := And (left associativity, at level 52).
Infix "∨" := Or (left associativity, at level 53).

Definition Implication (φ ψ : prop_formula) : prop_formula := ¬φ ∨ ψ.
Definition Equivalence (φ ψ : prop_formula) : prop_formula := φ ∧ ψ ∨ ¬φ ∧ ¬ψ.

Infix "→" := Implication (left associativity, at level 54).
Infix "↔" := Equivalence (left associativity, at level 55).

Fixpoint Interpretation (φ : prop_formula) (M : prop_variables -> bool) : bool := 
  match φ with
  | Var p => M p
  | ⊤ => true
  | ⊥ => false
  | ¬ψ => match Interpretation ψ M with 
         | true => false
         | false => true
         end
  | ψ ∧ υ => match (Interpretation ψ M), (Interpretation υ M) with 
            | false, _ => false
            | _, false => false
            | _, _ => true
            end
  | ψ ∨ υ => match (Interpretation ψ M), (Interpretation υ M) with 
            | true, _ => true
            | _, true => true
            | _, _ => false
            end
  end.

Definition Satisfies (φ : prop_formula) M  := (Interpretation φ M) = true.
Definition DoubleTurnstile φ ψ := forall M, (Satisfies φ M) -> (Satisfies ψ M).
Definition Tautology φ := forall M, Satisfies φ M.
Infix "⊨" := DoubleTurnstile (left associativity, at level 56).
Notation "_⊨" := Tautology.

Definition SemanticEquivalence φ ψ := and (φ ⊨ ψ) (ψ ⊨ φ).
Infix "~" := SemanticEquivalence (left associativity, at level 56).

Module Problem_1.

Theorem Problem_1_a: forall φ ψ : prop_formula,
  _⊨ (φ → ψ) <-> φ ⊨ ψ.
Proof.
  intros φ ψ.
  split.
  - intros H1. unfold Tautology in H1. unfold DoubleTurnstile. intros M1 H2.
    unfold Satisfies. unfold Satisfies in H1. unfold Satisfies in H1, H2.
    assert (H3: Interpretation (φ → ψ) M1 = true). { apply H1. }
    unfold Implication in H3. unfold Interpretation in  H2, H3.
    rewrite -> H2 in H3. 
    destruct (Interpretation ψ M1) eqn: E1.
    * reflexivity.
    * unfold Interpretation in E1. rewrite -> E1 in H3. discriminate H3.
  - intros H1. unfold Tautology. unfold DoubleTurnstile in H1. intros M1.
    unfold Satisfies. unfold Satisfies in H1.
    assert (H2: Interpretation φ M1 = true -> Interpretation ψ M1 = true). { apply H1. }
    unfold Implication.
    destruct (Interpretation φ M1) eqn: E1.
    * assert (H3: Interpretation ψ M1 = true). { apply H2. reflexivity. } 
      unfold Interpretation. unfold Interpretation in E1, H3. rewrite -> E1. rewrite H3. reflexivity.
    * unfold Interpretation. unfold Interpretation in E1. rewrite -> E1. reflexivity.
Qed.

Theorem Problem_1_b: forall φ ψ : prop_formula,
  _⊨ (φ ↔ ψ) <-> φ ~ ψ.
Proof.
  intros φ ψ.
  split.
  - intros H1. unfold SemanticEquivalence. unfold Tautology in H1.
    split.
    * unfold DoubleTurnstile. intros M1 H2.
      unfold Satisfies. unfold Satisfies in H1. unfold Satisfies in H1, H2.
      assert (H3: Interpretation (φ ↔ ψ) M1 = true). { apply H1. } 
      unfold Equivalence in H3. unfold Interpretation in H2, H3.
      rewrite -> H2 in H3.
      destruct (Interpretation ψ M1) eqn: E1.
      + reflexivity.
      + unfold Interpretation in E1. rewrite -> E1 in H3. discriminate H3. 
    * unfold DoubleTurnstile. intros M1 H2.
      unfold Satisfies. unfold Satisfies in H1. unfold Satisfies in H1, H2.
      assert (H3: Interpretation (φ ↔ ψ) M1 = true). { apply H1. } 
      unfold Equivalence in H3. unfold Interpretation in H2, H3.
      rewrite -> H2 in H3.
      destruct (Interpretation φ M1) eqn: E1.
      + reflexivity.
      + unfold Interpretation in E1. rewrite -> E1 in H3. discriminate H3.
  - intros H. unfold SemanticEquivalence in H. unfold Equivalence.
    destruct H as [ H1 H2 ]. unfold Tautology. intros M1.
    unfold Satisfies. unfold DoubleTurnstile in H1, H2. unfold Satisfies in H1, H2.
    assert (H3: Interpretation φ M1 = true -> Interpretation ψ M1 = true). { apply H1. }
    assert (H4: Interpretation ψ M1 = true -> Interpretation φ M1 = true). { apply H2. }
    destruct (Interpretation φ M1) eqn: Eφ.
    * assert (H5: Interpretation ψ M1 = true). { apply H3. reflexivity. }
      simpl. rewrite -> H5. rewrite -> Eφ. reflexivity.
    * destruct (Interpretation ψ M1) eqn: Eψ.
      + discriminate H4. reflexivity.
      + unfold Interpretation. unfold Interpretation in Eφ, Eψ. rewrite -> Eφ. rewrite -> Eψ. reflexivity.
Qed.

End Problem_1.

Module Problem_2.

Theorem Problem_2_a: forall φ : prop_formula,
  (¬¬φ)~φ.
Proof.
  intros φ. unfold SemanticEquivalence.
  split.
  - unfold DoubleTurnstile. unfold Satisfies. intros M1 H1. simpl in H1.
    destruct (Interpretation φ M1).
    * reflexivity.
    * discriminate H1.
  - unfold DoubleTurnstile. unfold Satisfies. intros M1 H1. simpl. rewrite -> H1. reflexivity.
Qed.

Theorem Problem_2_b: forall φ : prop_formula,
  _⊨ (φ ∨ ¬φ).
Proof.
  intros φ.
  unfold Tautology. intros M1. unfold Satisfies. unfold Interpretation.
  destruct (Interpretation φ M1) eqn: E1.
  - unfold Interpretation in E1. rewrite -> E1. reflexivity.
  - unfold Interpretation in E1. rewrite -> E1. reflexivity. 
Qed.

Theorem Problem_2_c: forall φ ψ η: prop_formula,
  φ ∧ (ψ ∨ η) ~ (φ ∧ ψ) ∨ (φ ∧ η).
Proof.
  intros φ ψ η. unfold SemanticEquivalence.
  split.
  - unfold DoubleTurnstile. intros M1. unfold Satisfies. intros H1.
    destruct (Interpretation φ M1) eqn: Eφ.
    * destruct (Interpretation ψ M1) eqn: Eψ.
      + unfold Interpretation in Eφ, Eψ. unfold Interpretation. rewrite -> Eφ. rewrite -> Eψ. reflexivity.
      + unfold Interpretation in Eφ, Eψ. 
        unfold Interpretation in H1. rewrite -> Eφ in H1. rewrite -> Eψ in H1.
        unfold Interpretation. rewrite -> Eφ. rewrite -> Eψ. rewrite -> H1. reflexivity.
    * unfold Interpretation in H1, Eφ. unfold Interpretation. rewrite -> Eφ. rewrite -> Eφ in H1. discriminate H1.
  - unfold DoubleTurnstile. intros M1. unfold Satisfies. intros H1.
    destruct (Interpretation φ M1) eqn: Eφ.
    * destruct (Interpretation ψ M1) eqn: Eψ.
      + unfold Interpretation in Eφ, Eψ. unfold Interpretation. rewrite -> Eφ. rewrite -> Eψ. reflexivity.
      + unfold Interpretation in Eφ, Eψ. 
        unfold Interpretation in H1. rewrite -> Eφ in H1. rewrite -> Eψ in H1.
        unfold Interpretation. rewrite -> Eφ. rewrite -> Eψ. rewrite -> H1. reflexivity.
    * unfold Interpretation in H1, Eφ. unfold Interpretation. rewrite -> Eφ. rewrite -> Eφ in H1. discriminate H1.
Qed.

Theorem Problem_2_d: forall φ ψ η: prop_formula,
  φ ∨ (ψ ∧ η) ~ (φ ∨ ψ) ∧ (φ ∨ η).
Proof.
  intros φ ψ η. unfold SemanticEquivalence.
  split.
  - unfold DoubleTurnstile. intros M1. unfold Satisfies. intros H1.
    destruct (Interpretation φ M1) eqn: Eφ.
    * unfold Interpretation in Eφ. unfold Interpretation. rewrite -> Eφ. reflexivity.
    * destruct (Interpretation ψ M1) eqn: Eψ.
      + unfold Interpretation in H1, Eφ, Eψ. unfold Interpretation.
        rewrite -> Eφ. rewrite -> Eψ. rewrite -> Eφ in H1. rewrite -> Eψ in H1. rewrite -> H1. reflexivity.
      + unfold Interpretation in H1, Eφ, Eψ. rewrite -> Eφ in H1. rewrite -> Eψ in H1. discriminate H1.
  - unfold DoubleTurnstile. intros M1. unfold Satisfies. intros H1.
    destruct (Interpretation φ M1) eqn: Eφ.
    * unfold Interpretation in Eφ. unfold Interpretation. rewrite -> Eφ. reflexivity.
    * destruct (Interpretation ψ M1) eqn: Eψ.
      + unfold Interpretation in H1, Eφ, Eψ. unfold Interpretation.
        rewrite -> Eφ. rewrite -> Eψ. rewrite -> Eφ in H1. rewrite -> Eψ in H1. rewrite -> H1. reflexivity.
      + unfold Interpretation in H1, Eφ, Eψ. rewrite -> Eφ in H1. rewrite -> Eψ in H1. discriminate H1.
Qed.

Theorem Problem_2_e: forall φ ψ: prop_formula,
  φ ∨ (φ ∧ ψ) ~ φ.
Proof.
  intros φ ψ. unfold SemanticEquivalence. unfold DoubleTurnstile.
  split.
  - intros M1. unfold Satisfies.
    destruct (Interpretation φ M1) eqn: E1.
    * reflexivity.
    * intros H1. unfold Interpretation in H1, E1. rewrite -> E1 in H1. discriminate H1.
  - intros M1. unfold Satisfies.
    destruct (Interpretation φ M1) eqn: E1.
    * intros H1. unfold Interpretation in E1. unfold Interpretation. rewrite -> E1. reflexivity.
    * intros H1. discriminate H1.
Qed.

Theorem Problem_2_f: forall φ ψ: prop_formula,
  φ ∧ (φ ∨ ψ) ~ φ.
Proof.
  intros φ ψ. unfold SemanticEquivalence. unfold DoubleTurnstile. unfold Satisfies. 
  split.
  - intros M1 H1.
    destruct (Interpretation φ M1) eqn: E1.
    * reflexivity.
    * unfold Interpretation in H1, E1. rewrite -> E1 in H1. discriminate H1.
  - intros M1 H1. unfold Interpretation in H1. unfold Interpretation. rewrite -> H1. reflexivity.
Qed.

Theorem Problem_2_g: forall φ ψ: prop_formula,
  ¬(φ ∧ ψ) ~ ¬φ ∨ ¬ψ.
Proof.
  intros φ ψ. unfold SemanticEquivalence. unfold DoubleTurnstile. unfold Satisfies. 
  split.
  - intros M1 H1.
    destruct (Interpretation φ M1) eqn: Eφ.
    * destruct (Interpretation ψ M1) eqn: Eψ.
      + unfold Interpretation in H1, Eφ, Eψ. rewrite -> Eφ in H1. rewrite -> Eψ in H1.
        unfold Interpretation. rewrite -> Eφ. rewrite -> Eψ.
        discriminate H1.
      + unfold Interpretation in Eφ, Eψ. unfold Interpretation. rewrite -> Eφ. rewrite -> Eψ. reflexivity.
    * destruct (Interpretation ψ M1) eqn: Eψ.
      + unfold Interpretation in Eφ. unfold Interpretation. rewrite -> Eφ. reflexivity.
      + unfold Interpretation in Eφ. unfold Interpretation. rewrite -> Eφ. reflexivity.
  - intros M1 H1.
    destruct (Interpretation φ M1) eqn: Eφ.
    * destruct (Interpretation ψ M1) eqn: Eψ.
      + unfold Interpretation in H1, Eφ, Eψ. rewrite -> Eφ in H1. rewrite -> Eψ in H1.
        unfold Interpretation. rewrite -> Eφ. rewrite -> Eψ.
        discriminate H1.
      + unfold Interpretation in Eφ, Eψ. unfold Interpretation. rewrite -> Eφ. rewrite -> Eψ. reflexivity.
    * destruct (Interpretation ψ M1) eqn: Eψ.
      + unfold Interpretation in Eφ. unfold Interpretation. rewrite -> Eφ. reflexivity.
      + unfold Interpretation in Eφ. unfold Interpretation. rewrite -> Eφ. reflexivity.
Qed.

Theorem Problem_2_h: forall φ ψ: prop_formula,
  ¬(φ ∨ ψ) ~ ¬φ ∧ ¬ψ.
Proof.
  intros φ ψ. unfold SemanticEquivalence. unfold DoubleTurnstile. unfold Satisfies. 
  split.
  - intros M1 H1.
    destruct (Interpretation φ M1) eqn: Eφ.
    * destruct (Interpretation ψ M1) eqn: Eψ.
      + unfold Interpretation in H1, Eφ, Eψ. rewrite -> Eψ in H1. rewrite -> Eφ in H1.
        unfold Interpretation. rewrite -> Eψ. rewrite -> Eφ.
        discriminate H1.
      + unfold Interpretation in H1, Eφ, Eψ. rewrite -> Eψ in H1. rewrite -> Eφ in H1.
        unfold Interpretation. rewrite -> Eψ. rewrite -> Eφ.
        discriminate H1.
    * destruct (Interpretation ψ M1) eqn: Eψ.
      + unfold Interpretation in H1, Eφ, Eψ. rewrite -> Eψ in H1. rewrite -> Eφ in H1.
        unfold Interpretation. rewrite -> Eψ. rewrite -> Eφ.
        discriminate H1.
      + unfold Interpretation in Eφ, Eψ. unfold Interpretation. rewrite -> Eψ. rewrite -> Eφ. reflexivity.
  - intros M1 H1.
    destruct (Interpretation φ M1) eqn: Eφ.
    * destruct (Interpretation ψ M1) eqn: Eψ.
      + unfold Interpretation in H1, Eφ, Eψ. rewrite -> Eψ in H1. rewrite -> Eφ in H1.
        unfold Interpretation. rewrite -> Eψ. rewrite -> Eφ.
        discriminate H1.
      + unfold Interpretation in H1, Eφ, Eψ. rewrite -> Eψ in H1. rewrite -> Eφ in H1.
        unfold Interpretation. rewrite -> Eψ. rewrite -> Eφ.
        discriminate H1.
    * destruct (Interpretation ψ M1) eqn: Eψ.
      + unfold Interpretation in H1, Eφ, Eψ. rewrite -> Eψ in H1. rewrite -> Eφ in H1.
        unfold Interpretation. rewrite -> Eψ. rewrite -> Eφ.
        discriminate H1.
      + unfold Interpretation in Eφ, Eψ. unfold Interpretation. rewrite -> Eψ. rewrite -> Eφ. reflexivity.
Qed.

End Problem_2.

Module Problem_3.

Theorem Problem_3_a: forall p q : prop_formula,
  _⊨ ((p → q) ↔ (¬q → ¬p)).
Proof.
  intros p q. unfold Tautology. intros M1. unfold Satisfies.
  destruct (Interpretation p M1) eqn: Ep.
    - destruct (Interpretation q M1) eqn: Eq.
      * unfold Interpretation in Ep, Eq. unfold Interpretation. simpl. rewrite -> Eq. rewrite -> Ep. reflexivity.
      * unfold Interpretation in Ep, Eq. unfold Interpretation. simpl. rewrite -> Eq. rewrite -> Ep. reflexivity.
    - destruct (Interpretation q M1) eqn: Eq.
      * unfold Interpretation in Ep, Eq. unfold Interpretation. simpl. rewrite -> Eq. rewrite -> Ep. reflexivity.
      * unfold Interpretation in Ep, Eq. unfold Interpretation. simpl. rewrite -> Eq. rewrite -> Ep. reflexivity.
Qed.

Theorem Problem_3_b: forall p q r : prop_formula,
  _⊨ ((p → (q → r)) ↔ (¬r → (¬q → ¬p))).
Proof.
  intros p q r. unfold Tautology. intros M1. unfold Satisfies.
  destruct (Interpretation p M1) eqn: Ep.
    - destruct (Interpretation q M1) eqn: Eq.
      * destruct (Interpretation r M1) eqn: Er.
        -- unfold Interpretation in Ep, Eq, Er. unfold Interpretation. simpl. 
           rewrite -> Eq. rewrite -> Ep. rewrite -> Er. reflexivity.
        -- unfold Interpretation in Ep, Eq, Er. unfold Interpretation. simpl. 
           rewrite -> Eq. rewrite -> Ep. rewrite -> Er. Abort.

(* 
  При интерпретации M:
    M[p] = true
    M[q] = true
    M[r] = false
  формула неверна. Т.е она необщезначимая,
  но при интерпретации M':
    M[p] = true
    M[q] = true
    M[r] = true
  формула выполнима.
 *)

End Problem_3.

Module Problem_4.

(*
  ННФ и КНФ:
  ¬(¬(p ∧ q) → ¬r) ~ ¬((p ∧ q) ∨ ¬r) ~ ¬(p ∧ q) ∧ r ~ (¬p ∨ ¬q) ∧ r
  (¬p ∨ ¬q) и r — дизъюнкты, т.е данная формула — конъюнкция дизъюнктов
 *)
Theorem Problem_4_a: forall p q r : prop_variables,
  ¬(¬((Var p) ∧ (Var q)) → ¬(Var r)) ~ (¬(Var p) ∨ ¬(Var q)) ∧ (Var r).
Proof.
  intros p q r. unfold SemanticEquivalence. unfold DoubleTurnstile. unfold Satisfies.
  split.
  - intros M1 H1.
    destruct (M1 p) eqn: Ep.
    * destruct (M1 q) eqn: Eq.
       + simpl in H1. rewrite -> Ep in H1. rewrite -> Eq in H1. discriminate H1.
       + destruct (M1 r) eqn: Er.
         -- simpl in H1. rewrite -> Ep in H1. rewrite -> Eq in H1. rewrite -> Er in H1.
            simpl. rewrite -> Ep. rewrite -> Eq. rewrite -> Er. reflexivity.
         -- simpl in H1. rewrite -> Ep in H1. rewrite -> Eq in H1. rewrite -> Er in H1.
            discriminate H1.
    * destruct (M1 r) eqn: Er.
      + simpl in H1. rewrite -> Ep in H1. rewrite -> Er in H1.
        simpl. rewrite -> Ep. rewrite -> Er. reflexivity.
      + simpl in H1. rewrite -> Ep in H1. rewrite -> Er in H1. discriminate H1.
  - intros M1 H1.
    destruct (M1 p) eqn: Ep.
    * destruct (M1 q) eqn: Eq.
       + simpl in H1. rewrite -> Ep in H1. rewrite -> Eq in H1. discriminate H1.
       + destruct (M1 r) eqn: Er.
         -- simpl in H1. rewrite -> Ep in H1. rewrite -> Eq in H1. rewrite -> Er in H1.
            simpl. rewrite -> Ep. rewrite -> Eq. rewrite -> Er. reflexivity.
         -- simpl in H1. rewrite -> Ep in H1. rewrite -> Eq in H1. rewrite -> Er in H1.
            discriminate H1.
    * destruct (M1 r) eqn: Er.
      + simpl in H1. rewrite -> Ep in H1. rewrite -> Er in H1.
        simpl. rewrite -> Ep. rewrite -> Er. reflexivity.
      + simpl in H1. rewrite -> Ep in H1. rewrite -> Er in H1. discriminate H1.
Qed.

(*
  ДНФ:
  ¬(¬(p ∧ q) → ¬r) ~ ¬((p ∧ q) ∨ ¬r) ~ ¬(p ∧ q) ∧ r ~ (¬p ∨ ¬q) ∧ r ~ (¬p ∧ r) ∨ (¬q ∧ r)
  (¬p ∧ r) и (¬q ∧ r) — конъюнкты, т.е данная формула — дизъюнкция конъюнктов
 *)
Theorem Problem_4_b: forall p q r : prop_variables,
  ¬(¬((Var p) ∧ (Var q)) → ¬(Var r)) ~ (¬(Var p) ∧ (Var r)) ∨ (¬(Var q) ∧ (Var r)).
Proof.
  intros p q r. unfold SemanticEquivalence. unfold DoubleTurnstile. unfold Satisfies.
  split.
  - intros M1 H1.
    destruct (M1 p) eqn: Ep.
    * destruct (M1 q) eqn: Eq.
       + simpl in H1. rewrite -> Ep in H1. rewrite -> Eq in H1. discriminate H1.
       + destruct (M1 r) eqn: Er.
         -- simpl in H1. rewrite -> Ep in H1. rewrite -> Eq in H1. rewrite -> Er in H1.
            simpl. rewrite -> Ep. rewrite -> Eq. rewrite -> Er. reflexivity.
         -- simpl in H1. rewrite -> Ep in H1. rewrite -> Eq in H1. rewrite -> Er in H1.
            discriminate H1.
    * destruct (M1 r) eqn: Er.
      + simpl in H1. rewrite -> Ep in H1. rewrite -> Er in H1.
        simpl. rewrite -> Ep. rewrite -> Er. reflexivity.
      + simpl in H1. rewrite -> Ep in H1. rewrite -> Er in H1. discriminate H1.
  - intros M1 H1.
    destruct (M1 p) eqn: Ep.
    * destruct (M1 q) eqn: Eq.
       + simpl in H1. rewrite -> Ep in H1. rewrite -> Eq in H1. discriminate H1.
       + destruct (M1 r) eqn: Er.
         -- simpl in H1. rewrite -> Ep in H1. rewrite -> Eq in H1. rewrite -> Er in H1.
            simpl. rewrite -> Ep. rewrite -> Eq. rewrite -> Er. reflexivity.
         -- simpl in H1. rewrite -> Ep in H1. rewrite -> Eq in H1. rewrite -> Er in H1.
            discriminate H1.
    * destruct (M1 r) eqn: Er.
      + simpl in H1. rewrite -> Ep in H1. rewrite -> Er in H1.
        simpl. rewrite -> Ep. rewrite -> Er. reflexivity.
      + simpl in H1. rewrite -> Ep in H1. rewrite -> Er in H1.
        destruct (M1 q) eqn: Eq.
        -- discriminate H1.
        -- discriminate H1.
Qed.

End Problem_4.

Module Problem_5.
End Problem_5.

Module Problem_6.
End Problem_6.

Module Problem_7.
End Problem_7.

Module Problem_8.
End Problem_8.

Module Problem_9.
End Problem_9.

Module Problem_10.
End Problem_10.