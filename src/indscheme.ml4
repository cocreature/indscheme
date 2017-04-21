(*i camlp4deps: "parsing/grammar.cma" i*)
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
(* for now the location of Forall' (a version of Forall based in Type) is hardcoded *)
let forall' = lazy (constant "foobar" ["Util"] "Forall'")
let forall_nil' = lazy (constant "foobar" ["Util"] "Forall_nil'")
let forall_cons' = lazy (constant "foobar" ["Util"] "Forall_cons'")

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
