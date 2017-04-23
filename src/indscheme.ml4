
(*i camlp4use: "pa_extend.cmo" i*)

DECLARE PLUGIN "indscheme"

open Vars
open Term
open Names
open Proofview.Goal
open Environ
open Loc
open Termops
open Inductiveops
open Inductive
open Feedback
open Printer

let constant locstr dir s = Universes.constr_of_global (Coqlib.find_reference locstr dir s)

let bind_ = lazy (constant "foobar" ["Autosubst"; "Autosubst_Classes"] "_bind")
let coq_list = lazy (constant "foobar" ["Coq"; "Init"; "Datatypes"] "list")
let coq_nil = lazy (constant "foobar" ["Coq"; "Init"; "Datatypes"] "nil")
let forall' = lazy (constant "foobar" ["Indscheme"; "Indscheme"] "Forall'")
let forall_nil' = lazy (constant "foobar" ["Indscheme"; "Indscheme"] "Forall_nil'")
let forall_cons' = lazy (constant "foobar" ["Indscheme"; "Indscheme"] "Forall_cons'")

let forall = lazy (constant "foobar" ["Coq"; "Lists"; "List"] "Forall")
let forall_nil = lazy (constant "foobar" ["Coq"; "Lists"; "List"] "Forall_nil")
let forall_cons = lazy (constant "foobar" ["Coq"; "Lists"; "List"] "Forall_cons")

let forall2 = lazy (constant "foobar" ["Coq"; "Lists"; "List"] "Forall2")
let forall2_nil = lazy (constant "foobar" ["Coq"; "Lists"; "List"] "Forall2_nil")
let forall2_cons = lazy (constant "foobar" ["Coq"; "Lists"; "List"] "Forall2_cons")


let build_forall el_ty list_ty env prop ind_el =
  let forall' = Lazy.force forall' in
  let forall_nil' = Lazy.force forall_nil' in
  let forall_cons' = Lazy.force forall_cons' in
  let fixp_ty = mkProd (Anonymous, list_ty, mkApp (forall', [|el_ty; prop; mkRel 1|])) in
  let (list_ind, _), _ = Inductive.find_rectype env (Lazy.force coq_list) in
  let case_info = make_case_info env list_ind MatchStyle in
  let returning = mkLambda (Anonymous, list_ty, mkApp (forall', [|el_ty; Vars.lift 2 prop; mkRel 1|])) in
  let body = mkCase (case_info,
                     returning, mkRel 1,
                     [|mkApp (forall_nil', [|el_ty; Vars.lift 1 prop|]);
                         (mkLambda (Anonymous, el_ty,
                          mkLambda (Anonymous, list_ty,
                                    mkApp (forall_cons',
                                           [|el_ty; Vars.lift 3 prop;
                                             mkRel 2; mkRel 1;
                                             mkApp (Vars.lift 3 ind_el, [|mkRel 2|]);
                                             mkApp (mkRel 4, [|mkRel 1|])|]))))|]) in
  mkApp (mkFix (([|0|], 0),
                ([|Anonymous|], [|fixp_ty|], [|mkLambda (Anonymous, list_ty, body)|])),
         [|mkRel 1|])

let handle_constr num_cases env rec_ty j i c =
  let rec handle_constr' c args ind_hy rec_call =
    match kind_of_term c with
    | Prod (_, t, c') ->
       let recurse =
         mkLambda (Anonymous, t,
                   handle_constr'
                     c'
                     (mkApp (mkRel rec_call, [|mkRel 1|])
                      :: mkRel 1
                      :: List.map (Vars.lift 1) args) (ind_hy + 1) (rec_call + 1)) in
       let passthrough =
         mkLambda (Anonymous, t,
                   handle_constr'
                     c'
                     (mkRel 1
                      :: List.map (Vars.lift 1) args) (ind_hy + 1) (rec_call + 1)) in
       if eq_constr rec_ty t then
         (* argument is rec_ty *)
         recurse
       else
         let coq_list = Lazy.force coq_list in
         let list_ty = mkApp (coq_list, [|rec_ty|]) in
         if eq_constr list_ty t then
           (* argument is a list of the rec_ty *)
           mkLambda (Anonymous, t,
                     handle_constr'
                       c'
                       (build_forall rec_ty list_ty env (mkRel (rec_call + num_cases + 2)) (mkRel (rec_call + 1))
                        :: mkRel 1
                        :: List.map (Vars.lift 1) args) (ind_hy + 1) (rec_call + 1))
         else
           let bind_ = Lazy.force bind_ in
           (match kind_of_term t with
            | App (op, _) ->
               if eq_constr op bind_ then
                 (* special case for autosubst binders *)
                 recurse
               else
                 passthrough
            | _ -> passthrough
           )
    | _ ->
       match args with
       | [] -> mkRel ind_hy
       | _ -> mkApp (mkRel ind_hy, Array.of_list (List.rev args))

  in handle_constr' c [] (j - i) 3

let rec wrap_in_lambda body ctx =
  match ctx with
  | [] -> body
  | (name, ty) :: ctx' -> wrap_in_lambda (mkLambda (name, ty, body)) ctx'

let indscheme =
  let open Sigma in
  Proofview.Goal.nf_enter { enter = begin fun gl ->
    let env = Proofview.Goal.env gl in
    let concl = Proofview.Goal.concl gl in
    let (_, n_ty) :: ctx, _ = decompose_prod concl in
    Refine.refine { run = begin fun sigma ->
      let fixp_ty = mkProd (Anonymous, n_ty, mkApp (mkRel (List.length ctx + 1), [|mkRel 1|])) in
      let env' = push_rels_assum ((Anonymous, n_ty) :: (Anonymous, fixp_ty) :: ctx) env in
      let (n_ind, _) as n_ind', _ = Inductive.find_rectype env' n_ty in
      let caseInfo = make_case_info env' n_ind MatchStyle in
      let n_constrs = Inductiveops.type_of_constructors env' n_ind' in
      let case = mkCase (caseInfo,
                         mkLambda (
                             Anonymous, n_ty,
                             mkApp (mkRel (List.length ctx + 1 + 2), [|mkRel 1|])),
                         mkRel 1,
                         Array.mapi (handle_constr (Array.length n_constrs) env' n_ty (List.length ctx + 1)) n_constrs) in
      let body = mkFix (([|0|], 0), ([|Anonymous|], [|fixp_ty|], [|mkLambda (Anonymous, n_ty, case)|])) in
      let r = wrap_in_lambda body ctx in
      Sigma (r, sigma, refl)
    end }
  end }

TACTIC EXTEND indscheme
| ["indscheme" ] -> [ indscheme ]
END

let pred_ty env pred =
  let (ind, u), _ = find_rectype env pred in
  let mind = lookup_mind_specif env ind in
  type_of_inductive env (mind, u)

let rec collect_args ty =
  match kind_of_term ty with
  | Prod (_, arg_ty, ty) -> arg_ty :: collect_args ty
  | _ -> []

let pred_arg_tys env pred =
  let ty = pred_ty env pred
  in collect_args ty

let splitAt n ls =
  if n <= 0 then ([], ls)
  else let rec splitAt' i xs =
         match xs with
         | [] -> ([], [])
         | (x :: xs') ->
            if i == 1 then ([x], xs')
            else let (xs'', xs''') = splitAt' (i-1) xs'
                 in (x :: xs'', xs''')
       in splitAt' n ls

let rec mk_prod_list body args =
  match args with
  | [] -> body
  | arg :: args' ->
      mk_prod_list (mkProd (Anonymous, arg, body)) args'

let rec mk_lambda_list body args =
  match args with
  |  [] -> body
  | arg :: args' ->
     mk_lambda_list (mkLambda (Anonymous, arg, body)) args'

let dest_ind_pred ind_pred (c : types) : (types array) option =
  match kind_of_term c with
  | App (op, args) ->
     if eq_constr op ind_pred
     then Some args
     else None
  | _ -> None

let dest_ind_pred_forall ind_pred c =
  match kind_of_term c with
  | App (op, args) ->
     let forall = Lazy.force forall in
     if eq_constr op forall
     then match args with
          | [|_;pred;arg|] ->
             if eq_constr pred ind_pred
             then Some arg
             else None
          | _ -> None
     else None
  | _ -> None

let dest_ind_pred_forall2 ind_pred c =
  msg_debug (print_constr c);
  match kind_of_term c with
  | App (op, args) ->
     let forall2 = Lazy.force forall2 in
     if eq_constr op forall2
     then match args with
          | [|_;_;pred;arg1;arg2|] ->
             if eq_constr pred ind_pred
             then Some (arg1, arg2)
             else None
          | _ -> None
     else None
  | _ -> None

let build_forall_fixp ind_pred goal_pred arg_ty env rec_call =
  let list = Lazy.force coq_list in
  let forall = Lazy.force forall in
  let forall_nil = Lazy.force forall_nil in
  let forall_cons = Lazy.force forall_cons in
  let coq_nil = Lazy.force coq_nil in
  let fix_ty =
    mkProd (Anonymous, mkApp (list, [|arg_ty|]),
            mkProd (Anonymous, mkApp (forall, [|arg_ty; ind_pred; mkRel 1|]),
                    mkApp (forall ,[|arg_ty; Vars.lift 3 goal_pred; mkRel 2|]))) in
  let env = push_rels_assum [
                             (Anonymous, mkApp (forall, [|arg_ty; ind_pred; mkRel 1|]));
                             (Anonymous, mkApp (list, [|arg_ty|]));
                             (Anonymous, fix_ty)
                            ] env in
  let forall_nil_case =
    mkApp (forall_nil, [|arg_ty; Vars.lift (3 + 1) goal_pred|]) in
  (* 7 refers to the inner recursive call because 4 args for forall_cons + Forall ind + list *)
  let forall_cons_case =
    mkLambda (Anonymous, arg_ty,
              mkLambda (Anonymous, mkApp (list, [|arg_ty|]),
                        mkLambda (Anonymous, mkApp (ind_pred, [|mkRel 2|]),
                                  mkLambda (Anonymous, mkApp (forall, [|arg_ty; ind_pred; mkRel 2|]),
                                            mkApp (forall_cons, [|arg_ty; Vars.lift (3 + 5) goal_pred; mkRel 4; mkRel 3;
                                                                  mkApp (Vars.lift 7 rec_call, [|mkRel 4; mkRel 2|]);
                                                                  mkApp (mkRel 7, [|mkRel 3; mkRel 1|])|]))))) in
  let (forall_ind, _), _ = Inductive.find_rectype env forall in
  let case_info = make_case_info env forall_ind MatchStyle in
  let returning =
    mkLambda (Anonymous, mkApp (list, [|arg_ty|]),
              mkLambda (Anonymous, mkApp (forall, [|arg_ty; ind_pred; mkRel 1|]),
                        mkApp (forall, [|arg_ty; Vars.lift (3 + 3) goal_pred; mkRel 2|]))) in
  let body =
    mkLambda (Anonymous, mkApp (list, [|arg_ty|]),
              mkLambda (Anonymous, mkApp (forall, [|arg_ty; ind_pred; mkRel 1|]),
                        mkCase (case_info, returning, mkRel 1,
                                [|forall_nil_case;forall_cons_case|]))) in
  mkFix (([|1|], 0),

         ([|Anonymous|], [|fix_ty|], [|body|]))

let build_forall2_fixp ind_pred goal_pred (arg_ty1, arg_ty2) env rec_call =
  let list = Lazy.force coq_list in
  let forall2 = Lazy.force forall2 in
  let forall2_nil = Lazy.force forall2_nil in
  let forall2_cons = Lazy.force forall2_cons in
  let coq_nil = Lazy.force coq_nil in
  let fix_ty =
    mkProd (Anonymous, mkApp (list, [|arg_ty1|]),
            mkProd (Anonymous, mkApp (list, [|arg_ty2|]),
                    mkProd (Anonymous, mkApp (forall2, [|arg_ty1; arg_ty2; ind_pred; mkRel 2; mkRel 1|]),
                            mkApp (forall2 ,[|arg_ty1; arg_ty2; Vars.lift 4 goal_pred; mkRel 3; mkRel 2|])))) in
  let env = push_rels_assum [
                             (Anonymous, mkApp (forall2, [|arg_ty1; arg_ty2; ind_pred; mkRel 2; mkRel 1|]));
                             (Anonymous, mkApp (list, [|arg_ty2|]));
                             (Anonymous, mkApp (list, [|arg_ty1|]));
                             (Anonymous, fix_ty)
                            ] env in
  let forall2_nil_case =
    mkApp (forall2_nil, [|arg_ty1; arg_ty2; Vars.lift 5 goal_pred|]) in
  let forall2_cons_case =
    mkLambda (Anonymous, arg_ty1,
    mkLambda (Anonymous, arg_ty2,
    mkLambda (Anonymous, mkApp (list, [|arg_ty1|]),
    mkLambda (Anonymous, mkApp (list, [|arg_ty2|]),
    mkLambda (Anonymous, mkApp (ind_pred, [|mkRel 4; mkRel 3|]),
    mkLambda (Anonymous, mkApp (forall2, [|arg_ty1; arg_ty2; ind_pred; mkRel 3; mkRel 2|]),
              mkApp (forall2_cons, [|arg_ty1; arg_ty2; Vars.lift 11 goal_pred; mkRel 6; mkRel 5; mkRel 4; mkRel 3;
                                    mkApp (Vars.lift 10 rec_call, [|mkRel 6; mkRel 5; mkRel 2|]);
                                    mkApp (mkRel 10, [|mkRel 4; mkRel 3; mkRel 1|])|]))))))) in
  let (forall2_ind, _), _ = Inductive.find_rectype env forall2 in
  let case_info = make_case_info env forall2_ind MatchStyle in
  let returning =
    mkLambda (Anonymous, mkApp (list, [|arg_ty1|]),
    mkLambda (Anonymous, mkApp (list, [|arg_ty2|]),
    mkLambda (Anonymous, mkApp (forall2, [|arg_ty1; arg_ty2; ind_pred; mkRel 2; mkRel 1|]),
                         mkApp (forall2, [|arg_ty1; arg_ty2; Vars.lift (3 + 5) goal_pred; mkRel 3; mkRel 2|])))) in
  let body =
    mkLambda (Anonymous, mkApp (list, [|arg_ty1|]),
    mkLambda (Anonymous, mkApp (list, [|arg_ty2|]),
    mkLambda (Anonymous, mkApp (forall2, [|arg_ty1; arg_ty2; ind_pred; mkRel 2; mkRel 1|]),
                         mkCase (case_info, returning, mkRel 1,
                                [|forall2_nil_case;forall2_cons_case|])))) in
  mkFix (([|2|], 0),
         ([|Anonymous|], [|fix_ty|], [|body|]))

let to_pair l =
  match l with
  | [x; y] -> (x, y)

let handle_constr_ty ind_pred goal_pred tys env arg_ref rec_call (arg : types) : types list =
  match dest_ind_pred ind_pred arg with
  | Some args -> [arg_ref; mkApp (rec_call, Array.append args [|arg_ref|])]
  | None ->
     match dest_ind_pred_forall ind_pred arg with
     | Some arg -> [arg_ref; mkApp (build_forall_fixp ind_pred goal_pred (List.hd tys) env rec_call, [|arg;arg_ref|])]
     | None ->
        match dest_ind_pred_forall2 ind_pred arg with
        | Some (arg1, arg2) -> [arg_ref; mkApp (build_forall2_fixp ind_pred goal_pred (to_pair tys) env rec_call, [|arg1;arg2;arg_ref|])]
        | None ->
           [arg_ref]

let handle_pred_constr ind_pred goal_pred tys env num_cases i c =
  msg_debug (print_constr c);
  let num_tys = List.length tys in
  let constr_args = collect_args c in
  let num_args = List.length constr_args in
  let basecase =
    applist (mkRel (num_tys + num_cases + 2 - i + num_args),
             List.concat
               (List.mapi
                  (fun i arg ->
                    handle_constr_ty
                      ind_pred
                      (Vars.lift num_args goal_pred)
                      tys
                      (push_rels_assum (List.map (fun t -> (Anonymous, t)) constr_args) env)
                      (mkRel (num_args - i))
                      (mkRel (num_args + num_tys + 2))
                      (Vars.lift (num_args - i) arg)) constr_args)) in
  let rec handle_pred_constr' c =
    match kind_of_term c with
    | Prod (_, ty, c) ->
       mkLambda (Anonymous, ty, handle_pred_constr' c)
    | _ -> basecase
  in handle_pred_constr' c

let build_match env ind_pred goal_pred tys =
  let (pred_ind, _) as pred_ind', _ = Inductive.find_rectype env ind_pred in
  let num_tys = List.length tys in
  let returning =
    Vars.lift (num_tys + 2) (
                mk_lambda_list
                  (mkLambda (Anonymous, applist (ind_pred, List.mapi (fun i _ -> mkRel (num_tys - i)) tys),
                             applist (goal_pred,
                                      List.mapi (fun i _ -> mkRel (1 + num_tys - i)) tys)))
                  tys) in
  let case_info = make_case_info env pred_ind MatchStyle in
  let constrs = Inductiveops.type_of_constructors env pred_ind' in
  let num_cases = Array.length constrs in
  mkCase (case_info,
          returning,
          mkRel 1,
          (Array.mapi (handle_pred_constr ind_pred goal_pred tys env num_cases) constrs))

let indscheme_pred =
  let open Sigma in
  Proofview.Goal.nf_enter
    { enter =
        begin fun gl ->
        let env = Proofview.Goal.env gl in
        let concl = Proofview.Goal.concl gl in
        let (_, applied_ind_pred) :: ctx, concl' = decompose_prod concl in
        let App (ind_pred, _) = kind_of_term applied_ind_pred in
        let App (goal_pred, _) = kind_of_term concl' in
        Refine.refine
          { run =
              begin fun sigma ->
              let tys = pred_arg_tys env ind_pred in
              let ctx', ctx'' = splitAt (List.length tys) ctx in
              let fixp_args = applied_ind_pred :: List.map snd ctx' in
              let goal_app =
                applist (goal_pred,
                         List.rev (List.mapi (fun i _ -> mkRel (i+2)) tys)) in
              let ind_app =
                applist (ind_pred,
                         List.rev (List.mapi (fun i _ -> mkRel (i+1)) tys)) in
              let fix_ty = mk_prod_list goal_app (ind_app :: tys) in
              let env'' = push_rels_assum ((Anonymous, fix_ty) :: ctx'') env in
              let env' = push_rels_assum ((Anonymous, ind_app) :: List.map (fun t -> (Anonymous, t)) tys) env'' in
              let match_expr = build_match env' ind_pred goal_pred tys in
              let fix_body = mk_lambda_list match_expr (ind_app :: tys) in
              let fixpoint = mkFix (([|List.length tys|], 0), ([|Anonymous|], [|fix_ty|], [|fix_body|])) in
              let final = mk_lambda_list fixpoint (List.map snd ctx'') in
              Sigma (final, sigma, refl)
              end
          }
        end
    }

TACTIC EXTEND indscheme_pred
| ["indscheme_pred"] -> [indscheme_pred]
END
