From iris.base_logic Require Export auth.
From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.

Section examples.
 Context `{heapG Σ}.

 Definition local_state : expr :=
  (λ: "f", let: "l" := Alloc #0 in "f" #();; !"l")%E.

 Lemma wp_local_state (f : val) : ∀ P Φ,
  {{ heap_ctx ★ {{ P }} f #() {{ Φ }} ★ P }}
  local_state f {{v, v = #0 ★ ∃ w, Φ w}}.
 Proof.
  iIntros (P Φ) "!# (#Hctx & Hf & HP)". unfold local_state.
  wp_value. wp_let.
  wp_alloc l as "Hl". wp_let. wp_bind (f _).
  iApply wp_wand_l. iSplitL "Hl"; last by iApply "Hf".
  iIntros (w) "HΦ". wp_seq. wp_load; iSplit; first done. iExists _; done.
 Qed.

 Definition local_state_lifted : expr :=
  (λ: "f", let: "l" := Alloc #0 in λ: <>, "f" #();; !"l")%E.

 Lemma wp_local_state_lifted (f : val) : ∀ P Φ,
  heap_ctx ★ {{ P }} f #() {{ Φ }} ⊢
  {{ True }} (local_state_lifted f)
   {{v, {{P}} (of_val v) #() {{u, u = #0 ★ ∃ w, Φ w}} }}.
 Proof.
  iIntros (P Φ) "[#Hctx #Hf]!# _". unfold local_state_lifted.
  wp_lam. wp_alloc l as "Hl".
  iMod (inv_alloc (nroot .@ "local_state_lifted") _ (l ↦ #0)%I with "[Hl]")
   as "#Hinv"; first by iNext.
  wp_let. iIntros "!# HP". wp_seq. wp_bind (f _).
  iApply wp_wand_l. iSplitR; last by iApply "Hf".
  iIntros (w) "HΦ". wp_seq.
  iInv (nroot .@ "local_state_lifted") as "Hl" "Hcl".
  wp_load. iMod ("Hcl" with "[Hl]") as "_"; first by iNext.
  iModIntro. iSplit; first done. iExists _; done.
 Qed.

 Definition shared_state : expr :=
  (let: "l" := Alloc #0 in λ: "f", "f" #();; !"l")%E.

 Lemma wp_shared_state :
  heap_ctx ⊢
  {{ True }} shared_state
   {{v, ∀ (f : val) P Φ,
        {{ {{ P }} f #() {{ Φ }} ★ P}} (of_val v) f {{u, u = #0 ★ ∃ w, Φ w}}
   }}.
 Proof.
  iIntros "#Hctx !# _". unfold shared_state.
  wp_alloc l as "Hl".
  iMod (inv_alloc (nroot .@ "shared_state") _ (l ↦ #0)%I with "[Hl]")
   as "#Hinv"; first by iNext.
  wp_let.
  iIntros (f P Φ) "!# [#Hf HP]". wp_let. wp_bind (f _).
  iApply wp_wand_l. iSplitR; last by iApply "Hf".
  iIntros (w) "HΦ". wp_seq.
  iInv (nroot .@ "shared_state") as "Hl" "Hcl".
  wp_load. iMod ("Hcl" with "[Hl]") as "_"; first by iNext.
  iModIntro. iSplit; first done. iExists _; done.
 Qed.

 Lemma wp_shared_state_2 :
  heap_ctx ⊢
  {{ True }}
   let: "g" := shared_state in "g" (λ: <>, "g" (λ: "x", "x");; #())
  {{v, v = #0 }}.
 Proof.
  iIntros "#Hctx !# _".
  wp_bind shared_state.
  iApply wp_wand_l; iSplitL; last (iApply (wp_shared_state with "[]"); done).
  iIntros (g) "#Hg". wp_let.
  iAssert (□ (WP (λ: <>, g (λ: "x", "x") ;; #()) #() {{ v, v = #() }}))%I as "#Hg'".
  - iIntros "!#". wp_lam.
    iAssert (□ (WP (λ: "x", "x") #() {{ v, v = #() }}))%I as "#Hg''";
     first by iIntros "!#"; wp_lam.
    wp_bind (g _).
    iApply wp_wand_r; iSplitL.
    + iApply ("Hg" $! (λ: "x", "x")%V True%I with "[Hg'']").
      iSplit; last done. iIntros "!# _"; done.
    + iIntros (w) "[Hw _]"; by wp_seq.
  - iApply wp_wand_r; iSplitL.
    iApply ("Hg" $! (λ: <>, g (λ: "x", "x") ;; #())%V True%I with "[]").
    iSplit; last done. iIntros "!# _"; done.
    iIntros (w) "[Hw _]"; done.
 Qed.

End examples.

Section Contradiction.

 Definition shared_state_ZO : expr :=
  (let: "l" := Alloc #0 in
   λ: "f", "l" <- #0;; "f" #();; "l" <- #1;; "f" #();; !"l")%E.

 Hypothesis wp_shared_state_ZO :
  ∀ Σ {Hhp : heapG Σ},
  heap_ctx ⊢
  {{ True }} shared_state_ZO
   {{v, ∀ (f : val) P Φ,
        {{ {{ P }} f #() {{ Φ }} ★ P}} (of_val v) f {{u, u = #1 ★ ∃ w, Φ w}}
   }}.

 Lemma wp_shared_state_ZO_2 :
  ∀ Σ {Hhp : heapG Σ},
  heap_ctx ⊢
  {{ True }}
   let: "g" := shared_state_ZO in "g" (λ: <>, "g" (λ: "x", "x");; #())
  {{v, v = #1 }}.
 Proof.
  iIntros (Σ Hhp) "#Hctx !# _".
  specialize (wp_shared_state_ZO Σ Hhp).
  wp_bind shared_state_ZO.
  iApply wp_wand_l; iSplitL; last (iApply (wp_shared_state_ZO with "[]"); done).
  iIntros (g) "#Hg". wp_let.
  iAssert (□ (WP (λ: <>, g (λ: "x", "x") ;; #()) #() {{ v, v = #() }}))%I as "#Hg'".
  - iIntros "!#". wp_lam.
    iAssert (□ (WP (λ: "x", "x") #() {{ v, v = #() }}))%I as "#Hg''";
     first by iIntros "!#"; wp_lam.
    wp_bind (g _).
    iApply wp_wand_r; iSplitL.
    + iApply ("Hg" $! (λ: "x", "x")%V True%I with "[Hg'']").
      iSplit; last done. iIntros "!# _"; done.
    + iIntros (w) "[Hw _]"; by wp_seq.
  - iApply wp_wand_r; iSplitL.
    iApply ("Hg" $! (λ: <>, g (λ: "x", "x") ;; #())%V True%I with "[]").
    iSplit; last done. iIntros "!# _"; done.
    iIntros (w) "[Hw _]"; done.
 Qed.

 Lemma Fork_wp_shared_state_ZO_2 :
  ∀ Σ {Hhp : heapG Σ},
  heap_ctx ⊢
  {{ True }}
   let: "g" := shared_state_ZO in
   Fork ("g" (λ: <>, "g" (λ: "x", "x");; #()));;
     "g" (λ: <>, "g" (λ: "x", "x");; #())
  {{v, v = #1 }}.
 Proof.
  iIntros (Σ Hhp) "#Hctx !# _".
  specialize (wp_shared_state_ZO Σ Hhp).
  wp_bind shared_state_ZO.
  iApply wp_wand_l; iSplitL; last (iApply (wp_shared_state_ZO with "[]"); done).
  iIntros (g) "#Hg". wp_let.
  iAssert (□ (WP (λ: <>, g (λ: "x", "x") ;; #()) #() {{ v, v = #() }}))%I
   as "#Hg'".
  - iIntros "!#". wp_lam.
    iAssert (□ (WP (λ: "x", "x") #() {{ v, v = #() }}))%I as "#Hg''";
     first by iIntros "!#"; wp_lam.
    wp_bind (g _).
    iApply wp_wand_r; iSplitL.
    + iApply ("Hg" $! (λ: "x", "x")%V True%I with "[Hg'']").
      iSplit; last done. iIntros "!# _"; done.
    + iIntros (w) "[Hw _]"; by wp_seq.
  - wp_bind (Fork _).
    iApply wp_wand_r; iSplitL.
    + iApply (wp_fork _ _ (λ w, w = #())%I with "[]").
      iNext; iSplit; first done.
      iApply wp_wand_r; iSplitL.
      iApply ("Hg" $! (λ: <>, g (λ: "x", "x") ;; #())%V True%I with "[]").
      iSplit; last done. iIntros "!# _"; done.
      iIntros (w) "[Hw _]"; done.
    + iIntros (w) "Hw". wp_seq.
      iApply wp_wand_r; iSplitL.
      iApply ("Hg" $! (λ: <>, g (λ: "x", "x") ;; #())%V True%I with "[]").
      iSplit; last done. iIntros "!# _"; done.
      iIntros (w') "[Hw' _]"; done.
 Qed.

 From iris.heap_lang Require Import adequacy.
 From iris.program_logic Require Import ectxi_language.
 From iris.algebra Require Import gmap.

 Let Σ : gFunctors := #[ heapΣ ].

 Lemma Fork_wp_shared_state_ZO_2_adequate :
   adequate (let: "g" := shared_state_ZO in
   Fork ("g" (λ: <>, "g" (λ: "x", "x");; #()));;
     "g" (λ: <>, "g" (λ: "x", "x");; #())) ∅ (λ w, w = #1).
 Proof.
  apply (@wp_adequacy Σ _ _). iIntros (?) "Hσ".
  iMod (auth_alloc to_heap ownP heapN _ ∅ with "[Hσ]") as (γ) "[Hc Hs]"; auto.
  - auto using to_heap_valid.
  - iApply (@Fork_wp_shared_state_ZO_2 Σ (HeapG _ _ _ γ) with "[Hc] []");
     last done.
    rewrite /heap_ctx /auth_ctx; done.
 Qed.

 (* single thread step *)
 Ltac SngTS :=
  econstructor;
    [match goal with
     |- step ([?A], _) _ =>
        eapply (step_atomic _ _ A _ _ _ [] [] []); simpl; eauto
    end | ].
 (* fist thread step *)
 Ltac FTS :=
  econstructor;
    [match goal with
     |- step ([?A; _], _) _ =>
        eapply (step_atomic _ _ A _ _ _ [] [] [_]); simpl; eauto
    end | ].

 (* second thread step *)
 Ltac STS :=
  econstructor;
    [match goal with
     |- step ([_; ?A], _) _ =>
        eapply (step_atomic _ _ A _ _ _ [] [_] []); simpl; eauto
    end | ].

 Ltac to_val_handle_closed :=
  simpl;
    match goal with
     |- match decide ?A with _ => _ end = _ =>
        assert A by apply _; let c := fresh in
         destruct (decide A) as [c|]; last tauto;
         match type of c with
          Closed ?A ?B => let e := W.of_expr B in
           replace c with (W.is_closed_correct A e I);
           first done; apply closed_proof_irrel
         end
       end.

 Theorem InConsistent_wp_shared_state_ZO : False.
 Proof.
  pose proof (Fork_wp_shared_state_ZO_2_adequate) as [Ha _]. simpl in *.
  cut (∃ e, rtc step
         ([(let: "g" := shared_state_ZO
            in Fork ("g" (λ: <>, "g" (λ: "x", "x") ;; #())) ;;
            "g" (λ: <>, "g" (λ: "x", "x") ;; #()))%E], ∅)
         ((of_val #0) :: [e], {[1%positive := #0]})).
  + intros [e Hstp]. specialize (Ha _ _ _ Hstp). done.
  + unfold shared_state_ZO.
    eexists.
    SngTS.
    eapply (Ectx_step _ _ _ _ [] [AppRCtx (λ: "g", _); AppRCtx (λ: "l", _)]
      (ref #0)%E (Lit $ LitLoc 1%positive)); eauto.
    eapply AllocS; first done. by rewrite lookup_empty. simpl.
    SngTS.
    eapply (Ectx_step _ _ _ _ [] [AppRCtx (λ: "g", _)]
      (_ (Lit $ LitLoc 1%positive))%E _); eauto; simpl.
    eapply BetaS; eauto. typeclasses eauto. rewrite /= /subst /=.
    SngTS.
    eapply (Ectx_step _ _ _ _ [] [] _ _); eauto; simpl.
    eapply BetaS; eauto; last typeclasses eauto.
    to_val_handle_closed.
    rewrite /= /subst /=.
    econstructor;
    [match goal with
     |- step ([?A], _) _ =>
        eapply (step_atomic _ _ A _ _ _ [_] [] []); simpl; eauto
    end | ].
    eapply (Ectx_step _ _ _ _ [_] [AppRCtx (λ: <>, _)] _ _); eauto; simpl.
    eapply ForkS. simpl.
    FTS.
    eapply (Ectx_step _ _ _ _ [] [] _ _); eauto; simpl.
    eapply BetaS; eauto; last typeclasses eauto.
    simpl.
    FTS.
    eapply (Ectx_step _ _ _ _ [] [] _ _); eauto; simpl.
    eapply BetaS; eauto; last typeclasses eauto.
    to_val_handle_closed.
    rewrite /= /subst /=.
    FTS.
    eapply (Ectx_step _ _ _ _ [] [AppRCtx (λ: <>, _)] _ _); eauto; simpl.
    eapply StoreS; first done.
    rewrite lookup_insert; eauto.
    simpl.
    FTS.
    eapply (Ectx_step _ _ _ _ [] [] _ _); eauto; simpl.
    eapply BetaS; eauto; last typeclasses eauto.
    rewrite /= /subst /=.
    FTS.
    eapply (Ectx_step _ _ _ _ [] [AppRCtx (λ: <>, _)] _ _); eauto; simpl.
    eapply BetaS; eauto; last typeclasses eauto.
    rewrite /= /subst /=.
    FTS.
    eapply (Ectx_step _ _ _ _ [] [AppRCtx (λ: <>, _); AppRCtx (λ: <>, _)] _ _);
     eauto; simpl.
    eapply BetaS; eauto; last typeclasses eauto.
    to_val_handle_closed.
    rewrite /= /subst /=.
    FTS.
    eapply (Ectx_step _ _ _ _ []
     [AppRCtx (λ: <>, _); AppRCtx (λ: <>, _); AppRCtx (λ: <>, _)] _ _);
     eauto; simpl.
    eapply StoreS; first done.
    rewrite lookup_insert; eauto.
    simpl.
    FTS.
    eapply (Ectx_step _ _ _ _ []
     [AppRCtx (λ: <>, _); AppRCtx (λ: <>, _)] _ _);
     eauto; simpl.
    eapply BetaS; eauto; last typeclasses eauto.
    rewrite /= /subst /=.
    FTS.
    eapply (Ectx_step _ _ _ _ []
      [AppRCtx (λ: <>, _); AppRCtx (λ: <>, _); AppRCtx (λ: <>, _)] _ _);
     eauto; simpl.
    eapply BetaS; eauto; last typeclasses eauto.
    rewrite /= /subst /=.
    FTS.
    eapply (Ectx_step _ _ _ _ []
     [AppRCtx (λ: <>, _); AppRCtx (λ: <>, _)] _ _);
     eauto; simpl.
    eapply BetaS; eauto; last typeclasses eauto.
    rewrite /= /subst /=.
    FTS.
    eapply (Ectx_step _ _ _ _ []
      [AppRCtx (λ: <>, _); AppRCtx (λ: <>, _); AppRCtx (λ: <>, _)] _ _);
     eauto; simpl.
    eapply StoreS; first done.
    rewrite lookup_insert; eauto.
    simpl.
    FTS.
    eapply (Ectx_step _ _ _ _ []
     [AppRCtx (λ: <>, _); AppRCtx (λ: <>, _)] _ _);
     eauto; simpl.
    eapply BetaS; eauto; last typeclasses eauto.
    rewrite /= /subst /=.
    FTS.
    eapply (Ectx_step _ _ _ _ []
     [AppRCtx (λ: <>, _); AppRCtx (λ: <>, _); AppRCtx (λ: <>, _)] _ _);
     eauto; simpl.
    eapply BetaS; eauto; last typeclasses eauto.
    rewrite /= /subst /=.
    FTS.
    eapply (Ectx_step _ _ _ _ []
     [AppRCtx (λ: <>, _); AppRCtx (λ: <>, _)] _ _);
     eauto; simpl.
    eapply BetaS; eauto; last typeclasses eauto.
    rewrite /= /subst /=.
    FTS.
    eapply (Ectx_step _ _ _ _ []
     [AppRCtx (λ: <>, _); AppRCtx (λ: <>, _)] _ _);
     eauto; simpl.
    eapply LoadS; eauto.
    rewrite /= /subst /=.
    FTS.
    eapply (Ectx_step _ _ _ _ [] [AppRCtx (λ: <>, _)] _ _); eauto; simpl.
    eapply BetaS; eauto; last typeclasses eauto.
    rewrite /= /subst /=.
    FTS.
    eapply (Ectx_step _ _ _ _ [] [] _ _); eauto; simpl.
    eapply BetaS; eauto; last typeclasses eauto.
    rewrite /= /subst /=.
    FTS.
    eapply (Ectx_step _ _ _ _ [] [AppRCtx (λ: <>, _)] _ _); eauto; simpl.
    eapply StoreS; first done.
    rewrite lookup_insert; eauto.
    simpl.
    FTS.
    eapply (Ectx_step _ _ _ _ [] [] _ _); eauto; simpl.
    eapply BetaS; eauto; last typeclasses eauto.
    rewrite /= /subst /=.
    FTS.
    eapply (Ectx_step _ _ _ _ [] [AppRCtx (λ: <>, _)] _ _); eauto; simpl.
    eapply BetaS; eauto; last typeclasses eauto.
    rewrite /= /subst /=.
    FTS.
    eapply (Ectx_step _ _ _ _ []
     [AppRCtx (λ: <>, _); AppRCtx (λ: <>, _)] _ _); eauto; simpl.
    eapply BetaS; eauto; last typeclasses eauto.
    to_val_handle_closed.
    rewrite /= /subst /=.
    FTS.
    eapply (Ectx_step _ _ _ _ []
      [AppRCtx (λ: <>, _); AppRCtx (λ: <>, _); AppRCtx (λ: <>, _)] _ _);
     eauto; simpl.
    eapply StoreS; first done.
    rewrite lookup_insert; eauto.
    simpl.
    FTS.
    eapply (Ectx_step _ _ _ _ []
     [AppRCtx (λ: <>, _); AppRCtx (λ: <>, _)] _ _);
     eauto; simpl.
    eapply BetaS; eauto; last typeclasses eauto.
    rewrite /= /subst /=.
    FTS.
    eapply (Ectx_step _ _ _ _ []
     [AppRCtx (λ: <>, _); AppRCtx (λ: <>, _); AppRCtx (λ: <>, _)] _ _);
     eauto; simpl.
    eapply BetaS; eauto; last typeclasses eauto.
    rewrite /= /subst /=.
    FTS.
    eapply (Ectx_step _ _ _ _ []
     [AppRCtx (λ: <>, _); AppRCtx (λ: <>, _)] _ _);
     eauto; simpl.
    eapply BetaS; eauto; last typeclasses eauto.
    rewrite /= /subst /=.
    FTS.
    eapply (Ectx_step _ _ _ _ []
     [AppRCtx (λ: <>, _); AppRCtx (λ: <>, _); AppRCtx (λ: <>, _)] _ _);
     eauto; simpl.
    eapply StoreS; first done.
    rewrite lookup_insert; eauto.
    rewrite /= /subst /=.
    FTS.
    eapply (Ectx_step _ _ _ _ []
     [AppRCtx (λ: <>, _); AppRCtx (λ: <>, _)] _ _); eauto; simpl.
    eapply BetaS; eauto; last typeclasses eauto.
    rewrite /= /subst /=.
    FTS.
    eapply (Ectx_step _ _ _ _ []
     [AppRCtx (λ: <>, _); AppRCtx (λ: <>, _); AppRCtx (λ: <>, _)] _ _);
     eauto; simpl.
    eapply BetaS; eauto; last typeclasses eauto.
    rewrite /= /subst /=.
    FTS.
    eapply (Ectx_step _ _ _ _ []
     [AppRCtx (λ: <>, _); AppRCtx (λ: <>, _)] _ _); eauto; simpl.
    eapply BetaS; eauto; last typeclasses eauto.
    rewrite /= /subst /=.
    FTS.
    eapply (Ectx_step _ _ _ _ []
     [AppRCtx (λ: <>, _); AppRCtx (λ: <>, _)] _ _); eauto; simpl.
    eapply LoadS; eauto.
    rewrite /= /subst /=.
    FTS.
    eapply (Ectx_step _ _ _ _ [] [AppRCtx (λ: <>, _)] _ _); eauto; simpl.
    eapply BetaS; eauto; last typeclasses eauto.
    rewrite /= /subst /=.
    FTS.
    eapply (Ectx_step _ _ _ _ [] [] _ _); eauto; simpl.
    eapply BetaS; eauto; last typeclasses eauto.
    rewrite /= /subst /=.
    STS.
    eapply (Ectx_step _ _ _ _ [] [] _ _); eauto; simpl.
    eapply BetaS; eauto; last typeclasses eauto.
    to_val_handle_closed.
    rewrite /= /subst /=.
    STS.
    eapply (Ectx_step _ _ _ _ [] [AppRCtx (λ: <>, _)] _ _); eauto; simpl.
    eapply StoreS; first done.
    rewrite lookup_insert; eauto.
    rewrite /= /subst /=.
    FTS.
    eapply (Ectx_step _ _ _ _ [] [] _ _); eauto; simpl.
    eapply LoadS; eauto.
    rewrite /= /subst /=.
    (* done *)
    match goal with
     |- rtc step ([_; _], ?A) ([_; _], ?B) => replace A with B
    end.
    apply rtc_refl.
    apply map_eq => i. destruct (decide (i = 1%positive)); subst.
    - by rewrite !lookup_insert.
    - by rewrite !lookup_insert_ne.
 Qed.

End Contradiction.