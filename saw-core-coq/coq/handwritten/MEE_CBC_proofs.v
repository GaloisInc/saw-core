From Coq          Require Import Init.Nat.
From Coq          Require Import Lists.List.
From Coq          Require Import Logic.Eqdep_dec.
From Coq          Require Import Omega.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.

From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra.
From CryptolToCoq Require Import Cryptol_proofs.
From CryptolToCoq Require Import MEE_CBC.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCorePreludeExtra.
From CryptolToCoq Require Import SAWCorePrelude_proofs.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

Import CryptolPrimitives.
Import SAWCorePrelude.

(*Notation "a" := (TCNum a) (at level 0, a at level 0, only printing).*)
Notation "a '+' b" := (tcAdd a b).
Notation "a '-' b" := (tcSub a b).
Notation "a '*' b" := (tcMul a b).
Notation "'Bit'" := (Bool).
Notation "b '[' a ']'" := (seq a b) (left associativity, at level 50).
Notation "'Byte'" := (seq (TCNum 8) Bool).
Notation "'🧙' a" := (coerce _ _ _ a) (at level 100, a at level 0, only printing).

Inductive finite : Num -> Prop :=
| TCNum_finite : forall n, finite (TCNum n)
.

Definition tcGe (a b : Num) : Prop :=
  match a, b with
  | TCNum a, TCNum b => ge a b
  | TCInf,   _       => Coq.Init.Logic.True
  | _,       TCInf   => Coq.Init.Logic.False
  end.

Notation "a '≥' b" := (tcGe a b) (at level 90, only printing).
Notation "'|' a '|'" := (tcWidth a) (only printing).

Definition blkBytes : Num := TCNum 16. (* TODO: translate me *)

Inductive pad_preconditions n p b :=
| mk_pad_preconditions :
      forall
        (fin_n   : finite n)
        (width_p : tcGe (TCNum 8) (tcWidth p))
        (p_eq    : p = tcSub (tcMul blkBytes b) n)
        (bound_n : tcGe (tcMul blkBytes b) n)
      ,
        pad_preconditions n p b
.

Inductive unpad_preconditions n p b :=
| mk_unpad_preconditions :
      forall
        (fin_n   : finite n)
        (width_p : tcGe (TCNum 8) (tcWidth p))
        (p_eq    : p = tcSub (tcMul blkBytes b) n)
        (bound_n : tcGe (tcMul blkBytes b) n)
      ,
        unpad_preconditions n p b
.

Theorem ecNumber_PLiteralSeqBool : forall n,
    ecNumber (TCNum n) Byte (PLiteralSeqBool (TCNum 8)) = bvNat 8 n.
Proof.
  reflexivity.
Qed.

Theorem rewriteRepeat T (x : T) n : repeat (TCNum n) _ x = Vector.const x n.
Proof.
  unfold repeat, seqMap.
  unfold Num_rect, map.
  induction n.
  { reflexivity. }
  {
    simpl in *.
    now f_equal.
  }
Qed.

Definition fin_seq_concat T m n :
    seq (TCNum m) T -> seq (TCNum n) T -> seq (tcAdd (TCNum m) (TCNum n)) T.
  simpl.
  rewrite rewrite_addNat.
  apply Vector.append.
Defined.

Theorem Nat__rec_S t o s n : Nat__rec t o s (S n) = s n (Nat__rec t o s n).
Proof.
  induction n; reflexivity.
Qed.

Theorem rewrite_ltNat m n : ltNat m n = ltb m n.
Proof.
  unfold ltNat.
  rewrite Nat_cases2_match_spec.
  revert m.
  induction n.
  {
    reflexivity.
  }
  {
    intros m.
    destruct m.
    {
      reflexivity.
    }
    {
      simpl.
      now rewrite IHn.
    }
  }
Qed.

Theorem ltb_add_left a b : a + b <? a = false.
Proof.
  destruct (PeanoNat.Nat.ltb_spec0 (a + b) a).
  { omega. }
  { reflexivity. }
Qed.

Theorem subNat_add m n : subNat (m + n)%nat m = n.
  unfold subNat.
  rewrite Nat_cases2_match_spec.
  induction m.
  {
    reflexivity.
  }
  {
    simpl.
    assumption.
  }
Qed.

Theorem rewrite_ecCat_TCNum m n a b :
    ecCat (TCNum m) (TCNum n) Byte a b = fin_seq_concat _ m n a b.
Proof.
  unfold ecCat.
  simpl.
  unfold append.
  unfold fin_seq_concat.
  rewrite rewrite_addNat.
  rewrite gen_add.
  f_equal.
  {
    rewrite gen_domain_eq with (g := fun i => sawAt m _ a i).
    {
      setoid_rewrite rewrite_ltNat.
      setoid_rewrite ltb_add_left.
      setoid_rewrite subNat_add.
      rewrite gen_sawAt.
      rewrite gen_sawAt.
      reflexivity.
    }
    {
      intros x XM.
      rewrite rewrite_ltNat.
      destruct (PeanoNat.Nat.ltb_spec0 x m).
      {
        reflexivity.
      }
      {
        intuition.
      }
    }
  }
Qed.

Theorem rewrite_ecCat m n a b :
    ecCat m n Byte a b =
    match m as m' return Byte [m'] -> Byte [m' + n] with
    | TCNum m' => fun a' =>
      match n as n' return Byte [n'] -> Byte [TCNum m' + n'] with
      | TCNum n' => fun b' => fin_seq_concat _ m' n' a' b'
      | _ => fun b' => streamAppend Byte _ a' b'
      end b
    | _ => fun a' =>
            error
              (forall (n0 : Num) (a0 : Type), a0 [TCInf] -> a0 [n0] -> a0 [TCInf + n0])
              "Unexpected Fin constraint violation!" n Byte a' b
    end a.
Proof.
  destruct m.
  {
    destruct n.
    {
      apply rewrite_ecCat_TCNum.
    }
    {
      reflexivity.
    }
  }
  {
    reflexivity.
  }
Qed.

Fixpoint join_fixpoint m n a (v : Vec m (Vec n a)) {struct v} : Vec (mulNat m n) a :=
  match v in Vector.t _ m' return Vec (mulNat m' n) a with
  | nil _ => nil _
  | cons _ h m' t => append _ _ _ h (join_fixpoint _ _ _ t)
  end.

Theorem rewrite_mulNat m n : mulNat m n = (m * n)%nat.
Proof.
  induction m.
  {
    reflexivity.
  }
  {
    simpl.
    rewrite rewrite_addNat.
    congruence.
  }
Defined.

Notation "<< Sig # C >> x" := (eq_rect _ Sig x _ C) (at level 65).
Notation "{{ Sig # x == y }}" := (existT Sig _ x = existT Sig _ y) (at level 50).

Definition typeId (T : Type) := T.

Theorem rewrite_divModNat m n : divModNat m n = (m / n, m mod n).
Proof.
  destruct n.
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    destruct (divmod m n 0 n).
    reflexivity.
  }
Qed.

Theorem rewrite_divNat m n : divNat m n = m / n.
Proof.
  unfold divNat.
  now rewrite rewrite_divModNat.
Qed.

Theorem rewrite_modNat m n : modNat m n = m mod n.
Proof.
  unfold modNat.
  now rewrite rewrite_divModNat.
Qed.

Theorem rewrite_append m n T a b :
    existT _ (addNat m n) (append m n T a b) =
    existT _ (m + n)%nat (Vector.append a b).
Proof.
  unfold append.
  induction a.
  {
    simpl.
    rewrite gen_sawAt.
    reflexivity.
  }
  {
    simpl.
    rewrite sawAt_zero.
    setoid_rewrite sawAt_S.
    dependent rewrite <- IHa.
    reflexivity.
  }
Qed.

Theorem rewrite_join' m n a v :
    existT (Vector.t a) (mulNat m n) (join m n a v) =
    existT (Vector.t a) (mulNat m n) (join_fixpoint m n a v).
Proof.
  induction v as [ | h i v ].
  {
    unfold join.
    simpl.
    reflexivity.
  }
  {
    unfold join.
    simpl.
    setoid_rewrite rewrite_modNat.
    setoid_rewrite rewrite_divNat.
    pattern (addNat n (mulNat i n)) at 1 2.
    rewrite rewrite_addNat.
    rewrite gen_add.
    rewrite gen_domain_eq with (g := fun i => sawAt n a h i).
    {
      rewrite gen_sawAt.
      unfold join in IHv.
      rewrite gen_domain_eq with (g := fun x => sawAt _ _ (sawAt _ _ v (divNat x n)) (modNat x n)).
      {
        apply inj_pair2_eq_dec in IHv.
        {
          rewrite IHv.
          rewrite rewrite_append.
          reflexivity.
        }
        {
          apply Peano_dec.eq_nat_dec.
        }
      }
      {
        rewrite rewrite_mulNat.
        intros m M.
        assert (0 < n) by (destruct n; omega).
        pose proof (Nat.lt_exists_pred 0 ((n + m) / n)) as P1.
        destruct P1 as [ x [ H1 H2 ] ].
        {
          pose proof (Nat.div_str_pos (n + m) n) as P2.
          apply P2.
          constructor; omega.
        }
        {
          simpl.
          rewrite H1.
          rewrite sawAt_S.
          pose proof (Nat.mod_add m 1 n) as P1.
          replace (m + 1 * n)%nat with (n + m)%nat in P1 by omega.
          rewrite P1.
          {
            rewrite rewrite_modNat.
            rewrite rewrite_divNat.
            f_equal.
            f_equal.
            pose proof (Nat.div_add m 1 n) as P2.
            replace (m + 1 * n)%nat with (n + m)%nat in P2 by omega.
            rewrite P2 in H1.
            {
              omega.
            }
            {
              omega.
            }
          }
          {
            omega.
          }
        }
      }
    }
    {
      intros m M.
      rewrite (Nat.mod_small m n M).
      rewrite (Nat.div_small m n M).
      rewrite sawAt_zero.
      reflexivity.
    }
  }
Qed.

Theorem rewrite_join m n a v : join m n a v = join_fixpoint m n a v.
Proof.
  apply (inj_pair2_eq_dec nat).
  {
    apply Peano_dec.eq_nat_dec.
  }
  {
    apply rewrite_join'.
  }
Qed.

Definition ecJoin_fixpoint m n a : a [n] [m] -> a [m * n] :=
  match m as m' return a [n] [m'] -> a [m' * n] with
  | TCNum m' =>
    match n as n' return forall a, Vec m' (a [n']) -> a [TCNum m' * n'] with
    | TCNum n' => join_fixpoint m' n'
    | TCInf => error _ "Unexpected Fin constraint violation!"
    end a
  | TCInf =>
    match n as n' return forall a, Stream (a [n']) -> a [TCInf * n'] with
    | TCNum n' =>
      match n' as n'' return forall a, Stream (a [TCNum n'']) -> a [TCInf * TCNum n''] with
      | 0     => fun a _ => nil a
      | S n'' => fun a s => streamJoin a n'' s (* TODO: do we want a co-inductive version? *)
      end
    | TCInf => error _ "Unexpected Fin constraint violation!"
    end a
  end.

Theorem rewrite_ecJoin m n a v : ecJoin m n a v = ecJoin_fixpoint m n a v.
Proof.
  destruct m.
  {
    unfold ecJoin_fixpoint.
    destruct n.
    {
      simpl.
      apply rewrite_join.
    }
    {
      simpl.
      reflexivity.
    }
  }
  {
    destruct n.
    {
      destruct n.
      {
        reflexivity.
      }
      {
        reflexivity.
      }
    }
    {
      simpl.
      reflexivity.
    }
  }
Qed.

Fixpoint split_fixpoint m n a {struct m} : Vec (mulNat m n) a -> Vec m (Vec n a).
Proof.
  intros v.
  induction m.
  {
    apply nil.
  }
  {
    apply cons.
    {
      simpl in v.
      eapply SAWCorePrelude.take.
      apply v.
    }
    {
      apply split_fixpoint.
      eapply SAWCorePrelude.drop.
      apply v.
    }
  }
Defined.

Theorem sawAt_drop T m n (v : Vec (addNat n m) T) i:
    sawAt _ _ (SAWCorePrelude.drop _ _ _ v) i =
    sawAt _ _ v (n + i)%nat.
Proof.
  induction n.
  {
    simpl.
    unfold SAWCorePrelude.drop.
    rewrite gen_sawAt.
    reflexivity.
  }
  {
    simpl in v.
    apply @Vector.caseS' with (v := v).
    intros h t.
    simpl.
    setoid_rewrite sawAt_S.
    rewrite <- IHn.
    f_equal.
  }
Qed.

Lemma rewrite_split m n a v : split m n a v = split_fixpoint m n a v.
Proof.
  induction m.
  {
    reflexivity.
  }
  {
    unfold split.
    simpl.
    f_equal.
    {
      rewrite <- IHm.
      unfold split.
      apply gen_domain_eq.
      intros i I.
      apply gen_domain_eq.
      intros j J.
      admit.
    }
  }
Admitted.

Lemma join_split s n (v : Byte [TCNum s * TCNum n]) :
    join_fixpoint s n (Vec 8 Bit) (split_fixpoint s n (Vec 8 Bit) v) = v.
Proof.
Admitted.

Theorem ecJoin_ecSplit m n v : ecJoin m n Byte (ecSplit m n Byte v) = v.
  rewrite rewrite_ecJoin.
  destruct m; destruct n; simpl.
  {
    rewrite rewrite_split.
    apply join_split.
  }
  {
    admit.
  }
  {
    admit.
  }
  {
    admit.
  }
Admitted.

Theorem fin_seq_concat_cons T m n h a b :
    fin_seq_concat T (S m) n (cons T h m a) b =
    cons T h (addNat m n) (fin_seq_concat T m n a b).
Proof.
  unfold fin_seq_concat.
  unfold eq_rect_r.
  simpl.
  unfold f_equal_nat.
  rewrite eq_sym_map_distr.
  destruct (eq_sym _).
  simpl.
  reflexivity.
Qed.

Theorem rewrite_fin_seq_concat T m n a b :
    existT (Vector.t T) (addNat m n) (fin_seq_concat T m n a b) =
    existT (Vector.t T) (m + n)%nat (Vector.append a b).
Proof.
  induction a.
  {
    compute.
    reflexivity.
  }
  {
    simpl.
    dependent rewrite <- IHa.
    f_equal.
    rewrite fin_seq_concat_cons.
    reflexivity.
  }
Qed.

Theorem sawAt_fin_seq_concat_left T m n a :
    forall b i,
    i < m ->
    sawAt (addNat m n) T (fin_seq_concat T m n a b) i = sawAt m T a i.
Proof.
  induction a as [ | h m t]; intros b i I.
  {
    omega.
  }
  {
    rewrite fin_seq_concat_cons.
    destruct i.
    {
      simpl.
      rewrite !sawAt_zero.
      reflexivity.
    }
    {
      simpl.
      rewrite !sawAt_S.
      apply IHt.
      omega.
    }
  }
Qed.

Theorem take_fin_seq_concat T m n a b :
    take (TCNum m) (TCNum n) T (fin_seq_concat T m n a b) = a.
Proof.
  induction a as [ | h m t ].
  {
    unfold take.
    unfold fin_seq_concat.
    simpl.
    unfold SAWCorePrelude.take.
    simpl.
    reflexivity.
  }
  {
    unfold take.
    simpl.
    unfold SAWCorePrelude.take.
    simpl.
    rewrite fin_seq_concat_cons.
    rewrite sawAt_zero.
    f_equal.
    setoid_rewrite sawAt_S.
    pose proof (sawAt_fin_seq_concat_left _ _ _ t b).
    rewrite gen_domain_eq with (g := fun i => sawAt _ _ t i).
    {
      apply gen_sawAt.
    }
    {
      intros i I.
      now apply sawAt_fin_seq_concat_left.
    }
  }
Qed.

Theorem pad_unpad n p b msg tag :
    pad_preconditions   n p b ->
    (* NOTE: those are the exact same as `pad_preconditions`, redundant *)
    (* unpad_preconditions n p b -> *)
    unpad n p b (pad n p b msg tag) = (msg, (tag, false)).
Proof.
  intros [].
  destruct n as [n|]; [clear fin_n|inversion fin_n].
  destruct p as [p|]; [|contradiction].
  destruct b as [b|]; [|inversion p_eq].
  unfold pad, unpad.
  rewrite ecNumber_PLiteralSeqBool.
  rewrite rewriteRepeat.
  f_equal.
  {
    rewrite rewrite_ecCat_TCNum.
    rewrite rewrite_ecCat.
    rewrite ecJoin_ecSplit.
    unfold coerce.

    unfold seq_cong1.
    unfold eq_cong.
    unfold Eq__rec.
    unfold identity_rect.

    Theorem plus_minus a b : a + b - a = b.
    Admitted.

    pattern (TCNum n + (TCNum 16 * (TCNum 2 + TCNum b) - TCNum n)).

    setoid_rewrite plus_minus.

    Axiom rewrite_sawUnsafeAssert : forall T x, sawUnsafeAssert T x x = identity_refl x.

    unfold sawUnsafeAssert.

    pattern (seq_cong1 (TCNum 16 * (TCNum 2 + TCNum b))) at 1.
    remember (TCNum 16 * (TCNum 2 + TCNum b) - TCNum n) as n1.
    cbn.
    unfold coerce.
    destruct seq_cong1.


    simpl.
    destruct (TCNum 32 + TCNum p).
    admit.
  }
  {
    f_equal.
    {
      admit.
    }
    {
      unfold ecEq.
      unfold Rget.
    }
  }
Admitted.
