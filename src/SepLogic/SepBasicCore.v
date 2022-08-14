From iris.proofmode Require Export base intro_patterns spec_patterns
     sel_patterns coq_tactics reduction
     coq_tactics ltac_tactics.
From iris Require Export bi.bi proofmode.tactics proofmode.monpred proofmode.reduction.

Local Ltac Fresh :=
  let x := iFresh in
  match x with
  | IAnon ?x =>
    let x := eval compute in (ascii_of_pos (x + 64)) in
        let x := eval compute in (append "H" (string_of_list_ascii [x])) in
            let env := iGetCtx in
            let P := reduction.pm_eval (envs_lookup x env) in
            match P with
            | None => x
            | Some _ => Fresh
            end
  | _ => fail "iFresh returns " x " sometimes."
  end.

(*h should be in the environment *)
Local Ltac norm h :=
  let env := iGetCtx in
  let P := reduction.pm_eval (envs_lookup h env) in
  match P with
  | None => fail "assert false"
  | Some (false, ?P) =>
    match P with
    | bi_exist ?Q => let x := fresh "x" in (iDestruct h as (x) h; norm h)
    | bi_sep ?Q ?W =>
      let x := Fresh in
      let y := Fresh in
      eapply tac_and_destruct with h _ x y _ _ _;
      [ pm_reflexivity | pm_reduce; iSolveTC | pm_reduce; norm x; norm y]
    | bi_pure (and ?P ?Q) =>
      let x := Fresh in
      eapply tac_and_destruct with h _ h x _ _ _;
      [pm_reflexivity
      |pm_reduce; iSolveTC
      |pm_reduce; norm h; norm x]
    | bi_pure _ => iPure h as ?
    | bi_wand _ _ => iDestruct (h with "[]") as h; [progress auto | norm h]
    | bi_absorbingly _ =>
      let name := Fresh in
      let name_mod := eval compute in (append ">" name) in
          iPoseProof h as name; iDestruct name as name_mod; norm name
    | _ =>
      match h with
      | IAnon _ =>
        let x := Fresh in
        iPoseProof h as x
      | _ => idtac
      end
    end
  | Some (true,?P) => idtac
  end.

(* (List.fold norm) in Ltac *)
Local Ltac norm_list l :=
  match l with
  | [] => idtac
  | ?h :: ?t => norm h ; norm_list t
  end.

Ltac norm_all :=
  iStartProof;
  let env := iGetCtx in
  let list_ident := eval compute in (rev (envs_dom env)) in
      norm_list list_ident; auto.

Tactic Notation "iNorm" := norm_all.

Lemma big_sepL_absorb_out : forall (biInd : biIndex) (PROP : bi) X (l : list X) (Q : X -> monPred biInd PROP),
    ⊢([∗ list] v ∈ l, <absorb> Q v) -∗
    <absorb> ([∗ list] v ∈ l, Q v).
Proof.
  induction l.
  - simpl. eauto.
  - simpl. iIntros (Q) "[HA HB]". iSplitL "HA". iFrame.
    iApply (IHl with "HB").
Qed.


Lemma big_sepL_double : forall (biInd : biIndex) (PROP : bi) X Y (l : list X) f (Q : Y -> monPred biInd PROP),
    ([∗ list] v ∈ l, [∗ list] v' ∈ f v, Q v') ⊢
      [∗ list] v ∈ list.foldr (fun v l => f v ++ l) [] l, Q v.
Proof.
  induction l; simpl; iIntros; iNorm.
  iApply big_sepL_app. iFrame. iApply (IHl with "HC").
Qed.

Lemma big_sepL_fold_mono :
  forall (biInd : biIndex) (PROP : bi) X Y v (l : list X) f (Q : Y -> monPred biInd PROP),
    (forall x, exists l', forall l, l' ++ l = f x l) ->
    ([∗ list] v ∈ list.foldr f v l, Q v) ⊣⊢
      ([∗ list] v ∈ v, Q v) ∗ ([∗ list] v ∈ list.foldr f [] l, Q v).
Proof.
  induction l; simpl; iIntros; iNorm.
  - iSplit; auto. iIntros "[$ _]".
  - iSplit.
    + iIntros "HA". destruct (H a) as [l' P0].
      do 2 rewrite <- P0. iDestruct (big_sepL_app with "HA") as "[HA HB]".
      iDestruct (IHl with "HB") as "[HB HC]".
      eauto. iFrame.
    + iIntros "[HA HB]". destruct (H a) as [l' P0].
      do 2 rewrite <- P0. iDestruct (big_sepL_app with "HB") as "[HB HC]".
      iApply big_sepL_app. iFrame. iApply IHl. auto.
      iFrame.
Qed.
