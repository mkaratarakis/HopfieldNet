import  HopfieldNet.CReals.CRcorrect
-- (*
-- Copyright © 2006-2008 Russell O’Connor

-- Permission is hereby granted, free of charge, to any person obtaining a copy of
-- this proof and associated documentation files (the "Proof"), to deal in
-- the Proof without restriction, including without limitation the rights to
-- use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
-- the Proof, and to permit persons to whom the Proof is furnished to do so,
-- subject to the following conditions:

-- The above copyright notice and this permission notice shall be included in all
-- copies or substantial portions of the Proof.

-- THE PROOF IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
-- IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
-- FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
-- COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
-- IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
-- CONNECTION WITH THE PROOF OR THE USE OR OTHER DEALINGS IN THE PROOF.
-- *)

-- Require Import CoRN.algebra.RSetoid.
-- Require Import CoRN.metric2.Metric.
-- Require Import CoRN.metric2.UniformContinuity.
-- Require Import CoRN.model.totalorder.QposMinMax.

-- Require Import CoRN.reals.fast.CRcorrect.
-- Require Import CoRN.model.metric2.Qmetric.

-- Require Export CoRN.reals.fast.CRFieldOps.
-- Require Export CoRN.model.ordfields.CRordfield.
-- Require Export CoRN.reals.CReals.
-- Require Import CoRN.tactics.CornTac.

-- Opaque CR.

-- Local Open Scope uc_scope.

-- (**
-- ** Example of a real number structure: $\langle$#&lang;#[CR]$\rangle$#&rang;#
-- *)

-- Lemma CRAbsSmall_ball : forall (x y:CR) (e:Q),
--     AbsSmall (R:=CRasCOrdField) (inject_Q_CR e) ((x:CRasCOrdField)[-]y) <->
--  ball e x y.
-- Proof.
--  intros x y e.
--  split.
--  - intros [H1 H2].
--   rewrite <- (doubleSpeed_Eq x).
--   rewrite <- (doubleSpeed_Eq (doubleSpeed x)).
--   rewrite <- (doubleSpeed_Eq y).
--   rewrite <- (doubleSpeed_Eq (doubleSpeed y)).
--   apply: regFunBall_e.
--   intros d.
--   assert (H1':=H1 d).
--   assert (H2':=H2 d).
--   clear H1 H2.
--   simpl.
--   set (x':=approximate x ((1#2)*((1#2)*d))%Qpos).
--   set (y':=approximate y ((1#2)*((1#2)*d))%Qpos).
--   change (-proj1_sig d <= x' - y' + - - e) in H1'.
--   change (-proj1_sig d <= e + - (x' - y')) in H2'.
--   rewrite -> Qle_minus_iff in *.
--   apply: ball_weak. apply Qpos_nonneg.
--   split; simpl; rewrite -> Qle_minus_iff.
--   rewrite Qopp_involutive. do 2 rewrite Qopp_involutive in H1'.
--   rewrite (Qplus_comm (proj1_sig d)).
--   rewrite Qplus_assoc. exact H1'.
--   rewrite <- Qplus_assoc, Qplus_comm. rewrite Qopp_involutive in H2'.
--   exact H2'.
--  - intros H.
--  rewrite <- (doubleSpeed_Eq x) in H.
--  rewrite <- (doubleSpeed_Eq y) in H.
--  split; intros d; destruct (H ((1#2)*d)%Qpos ((1#2)*d)%Qpos) as [H1 H2]; clear H;
--    set (x':=(approximate (doubleSpeed x) ((1 # 2) * d)%Qpos)) in *;
--      set (y':=(approximate (doubleSpeed y) ((1 # 2) * d)%Qpos)) in *.
--   autorewrite with QposElim in H1.
--   change (- ((1 # 2) * proj1_sig d + e + (1 # 2) * proj1_sig d)<=x' - y') in H1.
--   change (-proj1_sig d <= x' - y' + - - e).
--   rewrite -> Qle_minus_iff.
--   rewrite -> Qle_minus_iff in H1.
--   replace RHS with (x' - y' + - - ((1 # 2) * proj1_sig d + e + (1 # 2) * proj1_sig d)) by ring.
--   assumption.
--  autorewrite with QposElim in H2.
--  change (x' - y'<=((1 # 2) * proj1_sig d + e + (1 # 2) * proj1_sig d)) in H2.
--  change (-proj1_sig d <= e + - (x' - y')).
--  rewrite -> Qle_minus_iff.
--  rewrite -> Qle_minus_iff in H2.
--  replace RHS with ((1 # 2) * proj1_sig d + e + (1 # 2) * proj1_sig d + - (x' - y'))
--    by ring.
--  assumption.
-- Qed.

-- Lemma CRlt_Qlt : forall a b, (a < b)%Q -> ((' a%Q) < (' b))%CR.
-- Proof.
--  intros a b H.
--  destruct (Qpos_sub _ _ H) as [c Hc].
--  exists c.
--  intros d.
--  change (-proj1_sig d <= b + - a + - proj1_sig c).
--  rewrite -> Hc.
--  rewrite -> Qle_minus_iff.
--  ring_simplify.
--  apply Qpos_nonneg.
-- Qed.

-- Definition CRlim (s:CauchySeq CRasCOrdField) : CR.
-- Proof.
--  revert s.
--  intros [f Hf].
--  apply (ucFun (@Cjoin Q_as_MetricSpace)).
--  exists (fun e:QposInf => match e with | QposInfinity => 0%CR
--    | Qpos2QposInf e => let (n,_) := Hf (inject_Q_CR (proj1_sig e)) (CRlt_Qlt _ _ (Qpos_ispos e)) in f n end).
--  abstract ( intros e1 e2; destruct (Hf (inject_Q_CR (proj1_sig e1)) (CRlt_Qlt _ _ (Qpos_ispos e1))) as [n1 Hn1];
--    destruct (Hf (inject_Q_CR (proj1_sig e2)) (CRlt_Qlt _ _ (Qpos_ispos e2))) as [n2 Hn2];
--      eapply ball_triangle;[apply ball_sym|];rewrite <- CRAbsSmall_ball; [apply Hn1;apply Nat.le_max_l|
--        apply Hn2;apply Nat.le_max_r]) using Rlim_subproof0.
-- Defined.

-- Lemma CRisCReals : is_CReals CRasCOrdField CRlim.
-- Proof.
--  split.
--   intros [f Hf] e [d Hed].
--   destruct (Hf _ (CRlt_Qlt _ _ (Qpos_ispos ((1#2)*d)%Qpos))) as [n Hn].
--   exists n.
--   intros m Hm.
--   apply AbsSmall_leEq_trans with (inject_Q_CR (proj1_sig d));
--     [rstepr (e[-][0]);assumption|].
--   rewrite -> CRAbsSmall_ball.
--   change (nat -> Complete Q_as_MetricSpace) in f.
--   change (ball (proj1_sig d) (f m) (CRlim (Build_CauchySeq CRasCOrdField f Hf))).
--   rewrite <- (MonadLaw5 (f m)).
--   change (ball (proj1_sig d) (Cjoin (Cunit (f m))) (CRlim (Build_CauchySeq CRasCOrdField f Hf))).
--   unfold CRlim.
--   apply uc_prf.
--   change (ball (proj1_sig d) (Cunit (f m)) (Build_RegularFunction (Rlim_subproof0 f Hf))).
--   intros e1 e2.
--   simpl.
--   destruct (Hf (' proj1_sig e2)%CR (CRlt_Qlt _ _ (Qpos_ispos e2))) as [a Ha].
--   change (ball (proj1_sig (e1+d+e2)%Qpos) (f m) (f a)).
--   destruct (le_ge_dec a m).
--    rewrite <- CRAbsSmall_ball.
--    eapply AbsSmall_leEq_trans;[|apply Ha;assumption].
--    intros x.
--    autorewrite with QposElim.
--    change (-proj1_sig x <= proj1_sig e1 + proj1_sig d + proj1_sig e2 - proj1_sig e2).
--    rewrite -> Qle_minus_iff.
--    ring_simplify.
--    change (0<= proj1_sig (e1+d+x)%Qpos).
--    apply Qpos_nonneg.
--   apply ball_weak_le with (proj1_sig ((1#2)*d+(1#2)*d)%Qpos).
--    rewrite -> Qle_minus_iff.
--    simpl. ring_simplify.
--    change (0<= proj1_sig (e1+e2)%Qpos).
--    apply Qpos_nonneg.
--   apply ball_triangle with (f n);[|apply ball_sym]; rewrite <- CRAbsSmall_ball; apply Hn.
--    auto.
--   apply Nat.le_trans with m; auto.
--  (*Archimedean*)
--  intros x.
--  assert (X:=(CR_b_upperBound (1#1) x)).
--  destruct (CR_b (1 # 1) x) as [[n d] qpos].
--  destruct n as [|n|n]. inversion qpos. 2: inversion qpos.
--  rewrite (anti_convert_pred_convert n) in X.
--  exists (nat_of_P n)%nat.
--  eapply leEq_transitive.
--   apply X.
--  clear X.
--  intros z.
--  simpl.
--  unfold Cap_raw.
--  simpl.
--  apply Qle_trans with 0.
--   rewrite -> Qle_minus_iff.
--   ring_simplify.
--   apply Qpos_nonneg.
--  destruct (ZL4 n) as [a Ha].
--  rewrite Ha.
--  clear Ha.
--  simpl.
--  unfold Cap_raw.
--  simpl.
--  rewrite <- Qle_minus_iff.
--  remember ((1 # 2) * ((1 # 2) * z))%Qpos as q.
--  simpl in Heqq. rewrite <- Heqq. clear Heqq.
--  revert q.
--  induction a; intro q.
--   simpl.
--   ring_simplify.
--   unfold Qle.
--   simpl.
--   apply Zle_1_POS.
--  simpl.
--  unfold Cap_raw.
--  simpl.
--  rewrite -> Qle_minus_iff.
--  rewrite <- Qplus_assoc.
--  setoid_replace (1 + - (Pos.succ (Pos.of_succ_nat a) # d))
--    with (-((Pos.succ (Pos.of_succ_nat a) # d) - 1)) by ring.
--  rewrite<- Qle_minus_iff.
--  apply (Qle_trans _ (Pos.of_succ_nat a # d)).
--  2: apply IHa.
--  generalize (P_of_succ_nat a).
--  intros p.
--  rewrite -> Qle_minus_iff.
--  autorewrite with QposElim.
--  replace RHS with (((p#d) + 1) + - (Pos.succ p # d)) by ring.
--  rewrite <- Qle_minus_iff.
--  unfold Qle.
--  simpl.
--  repeat rewrite Pmult_1_r.
--  rewrite Pplus_one_succ_r.
--  repeat rewrite Zpos_mult_morphism.
--  apply Zmult_lt_0_le_compat_r.
--   auto with *.
--  repeat rewrite Zpos_plus_distr.
--  auto with *.
-- Qed.

-- Definition CRasCReals : CReals :=
-- Build_CReals _ _ CRisCReals.

-- Canonical Structure CRasCReals.
