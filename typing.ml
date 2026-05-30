exception NotImplemented
exception TypingError
exception UnifyError

type tyvarset = Core.tyvar Set_type.set
type tyscheme = tyvarset * Core.ty

let tvs0 : tyvarset = Set_type.empty

type venv = (Ast.vid, tyscheme * Core.is) Dict.dict
type tenv = (Ast.tycon, Core.tyname) Dict.dict
type env = venv * tenv

let ve0 : venv = Dict.empty
let te0 : tenv = Dict.empty
let env0 = (ve0, te0)

type sub = (Core.tyvar, Core.ty) Dict.dict

let sub0 : sub = Dict.empty

let rec subty (s : sub) (ty : Core.ty) : Core.ty =
  match ty with
  | Core.T_INT | Core.T_BOOL | Core.T_UNIT | Core.T_NAME _ -> ty
  | Core.T_PAIR (ty, ty') -> Core.T_PAIR (subty s ty, subty s ty')
  | Core.T_FUN (ty, ty') -> Core.T_FUN (subty s ty, subty s ty')
  | Core.T_VAR tv -> (
      match Dict.lookup tv s with Some ty -> subty s ty | None -> ty)

and subpat (s : sub) (pat : Core.pat) : Core.pat =
  match pat with
  | Core.P_WILD -> pat
  | Core.P_INT n -> pat
  | Core.P_BOOL b -> pat
  | Core.P_UNIT -> pat
  | Core.P_VID vid -> pat
  | Core.P_VIDP (vid, patty) -> Core.P_VIDP (vid, subpatty s patty)
  | Core.P_PAIR (patty, patty') ->
      Core.P_PAIR (subpatty s patty, subpatty s patty')

and subpatty (s : sub) (Core.PATTY (pat, ty)) : Core.patty =
  Core.PATTY (subpat s pat, subty s ty)

and subexp (s : sub) (exp : Core.exp) : Core.exp =
  match exp with
  | Core.E_FUN mlist -> Core.E_FUN (List.map (submrule s) mlist)
  | Core.E_APP (expty, expty') ->
      Core.E_APP (subexpty s expty, subexpty s expty')
  | Core.E_PAIR (expty, expty') ->
      Core.E_PAIR (subexpty s expty, subexpty s expty')
  | Core.E_LET (dec, expty) -> Core.E_LET (subdec s dec, subexpty s expty)
  | _ -> exp

and subexpty (s : sub) (Core.EXPTY (exp, ty)) : Core.expty =
  Core.EXPTY (subexp s exp, subty s ty)

and submrule (s : sub) (Core.M_RULE (patty, expty) : Core.mrule) : Core.mrule =
  Core.M_RULE (subpatty s patty, subexpty s expty)

and subdec (s : sub) (dec : Core.dec) : Core.dec =
  match dec with
  | Core.D_VAL (patty, expty) -> Core.D_VAL (subpatty s patty, subexpty s expty)
  | Core.D_REC (patty, expty) -> Core.D_REC (subpatty s patty, subexpty s expty)
  | Core.D_DTYPE -> dec

let rec subscheme (s : sub) ((tvs, ty) : tyscheme) : tyscheme =
  match tvs with
  | [] -> (tvs0, subty s ty)
  | tv :: tvs ->
      let tvs, ty =
        match Dict.lookup tv s with
        | Some _ -> (tvs, ty)
        | None -> subscheme s (tvs, ty)
        (* ^^ assertion: ((Core.T_VAR tv) : Core.ty) is not in sub(dict of vid:ty)'s ty *)
      in
      (tv :: tvs, ty)

and subvenv (s : sub) (ve : venv) : venv =
  Dict.map
    (fun (tscm, is) ->
      match is with Core.VAR -> (subscheme s tscm, is) | _ -> (tscm, is))
    ve

let subenv (s : sub) ((ve, te) : env) : env = (subvenv s ve, te)

let mergesub (s : sub) (s' : sub) : sub =
  (* s' overrides s. *)
  Dict.merge s s'

let newTyvar = ref 0

let genTyvar () =
  newTyvar := !newTyvar + 1;
  !newTyvar

let newTyname = ref 0

let genTyname () =
  newTyname := !newTyname + 1;
  !newTyname

let emptyScheme (ty : Core.ty) = (tvs0, ty)

let instScheme ((tvs, ty) : tyscheme) : Core.ty =
  let s =
    Set_type.fold
      (fun s tv ->
        let tv' = genTyvar () in
        Dict.insert (tv, Core.T_VAR tv') s)
      sub0 tvs
  in
  subty s ty

let rec ftvOfty (ty : Core.ty) : tyvarset =
  match ty with
  | Core.T_PAIR (ty, ty') -> Set_type.union (ftvOfty ty) (ftvOfty ty')
  | Core.T_FUN (ty, ty') -> Set_type.union (ftvOfty ty) (ftvOfty ty')
  | Core.T_VAR tv -> Set_type.singleton tv
  | _ -> tvs0

let ftvOfvenv (ve : venv) : tyvarset =
  Dict.map (fun ((tvs, ty), _) -> Set_type.diff (ftvOfty ty) tvs) ve
  |> Dict.range |> Set_type.collapse

let closure (ftvs : tyvarset) (ve : venv) : venv =
  Dict.map
    (fun ((tvs, ty), is) ->
      let tvs' = Set_type.diff (ftvOfty ty) ftvs in
      let tvs = Set_type.union tvs tvs' in
      ((tvs, ty), is))
    ve

let mergevenv (ve : venv) (ve' : venv) : venv =
  Dict.merge ve ve' (* ve' overrides ve. *)

let mergeenv ((ve, te) : env) ((ve', te') : env) : env =
  (mergevenv ve ve', Dict.merge te te')

let envOfvenv (ve : venv) : env = (ve, te0)
let envOftenv (te : tenv) : env = (ve0, te)
let var v = (v, Core.VAR)
let con v = (v, Core.CON)
let conf v = (v, Core.CONF)

let rec unify (ty : Core.ty) (ty' : Core.ty) : sub =
  match (ty, ty') with
  | ty, ty' when ty = ty' -> sub0
  | Core.T_PAIR (ty1, ty2), Core.T_PAIR (ty1', ty2')
  | Core.T_FUN (ty1, ty2), Core.T_FUN (ty1', ty2') ->
      let s = unify ty2 ty2' in
      let s' = unify (subty s ty1) (subty s ty1') in
      mergesub s' s
  | Core.T_VAR tv, ty | ty, Core.T_VAR tv ->
      if Set_type.mem tv (ftvOfty ty) then raise UnifyError
      else Dict.singleton (tv, ty)
  | _ -> raise UnifyError

let rec tty (te : tenv) (ty : Ast.ty) : Core.ty =
  match ty with
  | Ast.T_INT -> Core.T_INT
  | Ast.T_BOOL -> Core.T_BOOL
  | Ast.T_UNIT -> Core.T_UNIT
  | Ast.T_CON tc ->
      Core.T_NAME
        (match Dict.lookup tc te with
        | None -> raise TypingError
        | Some tn -> tn)
  | Ast.T_PAIR (t, t') -> Core.T_PAIR (tty te t, tty te t')
  | Ast.T_FUN (t, t') -> Core.T_FUN (tty te t, tty te t')

let rec tpat ((ve, te) : env) (pat : Ast.pat) : venv * Core.patty =
  match pat with
  | Ast.P_WILD ->
      let tv = genTyvar () in
      let ty = Core.T_VAR tv in
      (ve0, Core.PATTY (Core.P_WILD, ty))
  | Ast.P_INT n -> (ve0, Core.PATTY (Core.P_INT n, Core.T_INT))
  | Ast.P_BOOL b -> (ve0, Core.PATTY (Core.P_BOOL b, Core.T_BOOL))
  | Ast.P_UNIT -> (ve0, Core.PATTY (Core.P_UNIT, Core.T_UNIT))
  | Ast.P_VID vid -> (
      match Dict.lookup vid ve with
      | Some ((_, ty), Core.CON) -> (ve0, Core.PATTY (Core.P_VID (con vid), ty))
      | _ ->
          let tv = genTyvar () in
          let ty = Core.T_VAR tv in
          let ve' : venv = Dict.singleton (vid, var (tvs0, ty)) in
          (ve', Core.PATTY (Core.P_VID (var vid), ty)))
  | Ast.P_VIDP (vid, pat) -> (
      match Dict.lookup vid ve with
      | Some ((_, Core.T_FUN (_, ty)), Core.CONF) ->
          let ve', patty = tpat (ve, te) pat in
          (ve', Core.PATTY (Core.P_VIDP (conf vid, patty), ty))
      | _ -> failwith "tpat: should not match here")
  | Ast.P_PAIR (pat1, pat2) ->
      let ve1, (Core.PATTY (pat1, ty1) as patty1) = tpat (ve, te) pat1 in
      let ve2, (Core.PATTY (pat2, ty2) as patty2) = tpat (ve, te) pat2 in
      ( mergevenv ve1 ve2,
        Core.PATTY (Core.P_PAIR (patty1, patty2), Core.T_PAIR (ty1, ty2)) )
  | Ast.P_TPAT (pat, ty) ->
      let ty = tty te ty in
      let ve', (Core.PATTY (_, ty') as patty) = tpat (ve, te) pat in
      let s = unify ty ty' in
      (subvenv s ve', subpatty s patty)

let tconbinding (te : tenv) (tn : Core.tyname) (conbinding : Ast.conbinding) :
    env =
  let ve : venv =
    match conbinding with
    | Ast.CB_VID vid ->
        let ty = Core.T_NAME tn in
        let tvs = ftvOfty ty in
        Dict.singleton (vid, con (tvs, ty))
    | Ast.CB_TVID (vid, ty) ->
        let ty = Core.T_FUN (tty te ty, Core.T_NAME tn) in
        let tvs = ftvOfty ty in
        Dict.singleton (vid, conf (tvs, ty))
  in
  (ve, te)

let rec texp (env : env) (exp : Ast.exp) : sub * Core.expty =
  match exp with
  | Ast.E_INT n -> (sub0, Core.EXPTY (Core.E_INT n, Core.T_INT))
  | Ast.E_BOOL b -> (sub0, Core.EXPTY (Core.E_BOOL b, Core.T_BOOL))
  | Ast.E_UNIT -> (sub0, Core.EXPTY (Core.E_UNIT, Core.T_UNIT))
  | Ast.E_PLUS ->
      ( sub0,
        Core.EXPTY
          ( Core.E_PLUS,
            Core.T_FUN (Core.T_PAIR (Core.T_INT, Core.T_INT), Core.T_INT) ) )
  | Ast.E_MINUS ->
      ( sub0,
        Core.EXPTY
          ( Core.E_MINUS,
            Core.T_FUN (Core.T_PAIR (Core.T_INT, Core.T_INT), Core.T_INT) ) )
  | Ast.E_MULT ->
      ( sub0,
        Core.EXPTY
          ( Core.E_MULT,
            Core.T_FUN (Core.T_PAIR (Core.T_INT, Core.T_INT), Core.T_INT) ) )
  | Ast.E_EQ ->
      ( sub0,
        Core.EXPTY
          ( Core.E_EQ,
            Core.T_FUN (Core.T_PAIR (Core.T_INT, Core.T_INT), Core.T_BOOL) ) )
  | Ast.E_NEQ ->
      ( sub0,
        Core.EXPTY
          ( Core.E_NEQ,
            Core.T_FUN (Core.T_PAIR (Core.T_INT, Core.T_INT), Core.T_BOOL) ) )
  | Ast.E_VID vid -> (
      let ve, _ = env in
      match Dict.lookup vid ve with
      | None -> raise TypingError
      | Some (tscm, is) ->
          let ty = instScheme tscm in
          (sub0, Core.EXPTY (Core.E_VID (vid, is), ty)))
  | Ast.E_FUN mlist ->
      let s, ty, mlist = tmatch env mlist in
      (s, Core.EXPTY (Core.E_FUN mlist, ty))
  | Ast.E_APP (exp1, exp2) ->
      let s1, expty1 = texp env exp1 in
      let env = subenv s1 env in
      let s2, (Core.EXPTY (_, ty2) as expty2) = texp env exp2 in
      let (Core.EXPTY (_, ty1) as expty1) = subexpty s2 expty1 in
      let tv = genTyvar () in
      let ty3 = Core.T_VAR tv in
      let s3 = unify ty1 (Core.T_FUN (ty2, ty3)) in
      ( mergesub s3 (mergesub s2 s1),
        Core.EXPTY
          (Core.E_APP (subexpty s3 expty1, subexpty s3 expty2), subty s3 ty3) )
  | Ast.E_PAIR (exp1, exp2) ->
      let s1, expty1 = texp env exp1 in
      let env = subenv s1 env in
      let s2, (Core.EXPTY (_, ty2) as expty2) = texp env exp2 in
      let (Core.EXPTY (_, ty1) as expty1) = subexpty s2 expty1 in
      ( mergesub s2 s1,
        Core.EXPTY (Core.E_PAIR (expty1, expty2), Core.T_PAIR (ty1, ty2)) )
  | Ast.E_LET (dec, exp) ->
      let s1, env, dec = tdec env dec in
      let s2, (Core.EXPTY (_, ty) as expty) = texp env exp in
      let dec = subdec s2 dec in
      (mergesub s2 s1, Core.EXPTY (Core.E_LET (dec, expty), ty))
  | Ast.E_TEXP (exp, ty) ->
      let _, te = env in
      let ty = tty te ty in
      let s1, (Core.EXPTY (_, ty') as expty) = texp env exp in
      let s2 = unify ty ty' in
      let expty = subexpty s2 expty in
      (mergesub s2 s1, expty)

and tmatch ((ve, te) : env) (mlist : Ast.mrule list) :
    sub * Core.ty * Core.mrule list =
  let s, ty, mlist_rev =
    List.fold_left
      (fun (s, ty, mlist_rev) (Ast.M_RULE (pat, exp)) ->
        let ve, te = subenv s (ve, te) in
        let ve_pat, patty = tpat (ve, te) pat in
        let s1, (Core.EXPTY (_, ty2) as expty) =
          texp (mergevenv ve ve_pat, te) exp
        in
        (* let ve = subvenv s1 ve in *)
        let (Core.PATTY (_, ty1) as patty) = subpatty s1 patty in
        let ty, s2 =
          match ty with
          | Some ty -> (ty, unify ty (Core.T_FUN (ty1, ty2)))
          | None -> (Core.T_FUN (ty1, ty2), sub0)
        in
        let ty = subty s2 ty in
        let patty = subpatty s2 patty in
        let expty = subexpty s2 expty in
        let s' = mergesub s2 s1 in
        (* let ve_pat = subvenv s' ve_pat in
        let ve_pat = closure (ftvOfvenv ve) ve_pat in *)
        let mlist_rev = List.map (submrule s') mlist_rev in
        (mergesub s' s, Some ty, Core.M_RULE (patty, expty) :: mlist_rev))
      (sub0, None, []) mlist
  in
  let ty =
    match ty with Some ty -> ty | None -> failwith "should not match here"
  in
  (s, subty s ty, List.rev mlist_rev)

and tdec ((ve, te) : env) (dec : Ast.dec) : sub * env * Core.dec =
  match dec with
  | Ast.D_VAL (pat, exp) ->
      let ve_pat, patty = tpat (ve, te) pat in
      let s1, (Core.EXPTY (_, ty2) as expty) = texp (ve, te) exp in
      let ve = subvenv s1 ve in
      let (Core.PATTY (_, ty1) as patty) = subpatty s1 patty in
      let s2 = unify ty1 ty2 in
      let patty = subpatty s2 patty in
      let expty = subexpty s2 expty in
      let s = mergesub s2 s1 in
      let ve_pat = subvenv s ve_pat in
      let ve_pat = closure (ftvOfvenv ve) ve_pat in
      (s, (mergevenv ve ve_pat, te), Core.D_VAL (patty, expty))
  | Ast.D_REC (pat, exp) ->
      let ve_pat, patty = tpat (ve, te) pat in
      let s1, (Core.EXPTY (_, ty2) as expty) =
        texp (mergevenv ve ve_pat, te) exp
      in
      let ve = subvenv s1 ve in
      let (Core.PATTY (_, ty1) as patty) = subpatty s1 patty in
      let s2 = unify ty1 ty2 in
      let patty = subpatty s2 patty in
      let expty = subexpty s2 expty in
      let s = mergesub s2 s1 in
      let ve_pat = subvenv s ve_pat in
      let ve_pat = closure (ftvOfvenv ve) ve_pat in
      (s, (mergevenv ve ve_pat, te), Core.D_REC (patty, expty))
  | Ast.D_DTYPE (tc, cblist) ->
      let tn = genTyname () in
      let te = Dict.insert (tc, tn) te in
      let env =
        List.map (tconbinding te tn) cblist |> List.fold_left mergeenv (ve, te)
      in
      (sub0, env, Core.D_DTYPE)

let tprogram ((dlist : Ast.dec list), (exp : Ast.exp)) :
    Core.dec list * Core.expty =
  (* TODO: check if it's ok that s is unused at all *)
  let (s, env), dlist =
    List.fold_left_map
      (fun (s, env) dec ->
        let s', env, dec = tdec env dec in
        ((mergesub s' s, env), dec))
      (sub0, env0) dlist
  in
  let s', expty = texp env exp in
  let dlist = List.map (subdec s') dlist in
  (dlist, expty)
