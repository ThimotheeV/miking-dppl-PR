include "mlang/ast.mc"
include "mlang/ast-builder.mc"
include "../coreppl.mc"
include "../dist.mc"

lang AutoDriftKernel = Assume + DistAll + LetAsDecl
  sem generateKernels : Float -> Expr -> Expr
  sem generateKernels driftScale =
  | tm -> smap_Expr_Expr (generateKernels driftScale) tm
  | TmAssume (x & {driftKernel = None ()}) ->
    let dist = generateKernels driftScale x.dist in
    let res = chooseKernel driftScale dist in
    let assume = TmAssume {x with dist = res.distribution, driftKernel = Some res.driftKernelF} in
    foldr (lam d. lam e. declAsExpr e d) assume res.shared

  sem _defaultKernel : Float -> Expr -> {shared : [Decl], distribution : Expr, driftKernelF : Expr}
  sem _defaultKernel driftScale = | dist ->
    let distName = nameSym "dist" in
    let info = infoTm dist in
    { shared = [declWithInfo info (decl_nulet_ distName dist)]
    , distribution = withInfo info (nvar_ distName)
    , driftKernelF = withInfo info (ulam_ "" (withInfo info (nvar_ distName)))
    }

  sem chooseKernel : Float -> Expr -> {shared : [Decl], distribution : Expr, driftKernelF : Expr}
  sem chooseKernel driftScale =
  | dist -> _defaultKernel driftScale dist
  | dist & TmDist x ->
    let xName = nameSym "x" in
    match chooseKernelDist (float_ driftScale) (nvar_ xName) x.dist with Some driftKernelF then
      { shared = []
      , distribution = dist
      , driftKernelF = withInfo x.info (nulam_ xName driftKernelF)
      }
    else _defaultKernel driftScale dist
  | TmDist (x & {dist = DCategorical args}) ->
    match
      match args.p with TmVar _ then ([], args.p) else
      let argName = nameSym "p" in
      ([decl_nulet_ argName args.p], withInfo x.info (nvar_ argName))
    with (shared, p) in
    let prevName = nameSym "x" in
    let driftP = set_ p (nvar_ prevName) (float_ 0.0) in
    let driftP = map_ (ulam_ "p" (divf_ (var_ "p") (subf_ (float_ 1.) (get_ p (nvar_ prevName))))) driftP in
    { shared = shared
    , distribution = TmDist {x with dist = DCategorical {p = p}}
    , driftKernelF = withInfo x.info (nulam_ prevName (dist_ (DCategorical {p = driftP})))
    }

  sem chooseKernelDist : Expr -> Expr -> Dist -> Option Expr
  sem chooseKernelDist driftScale x =
  | _ -> None ()

  -- exp = x, var = x*(1 - x)/(drift + 1) --
  | DBeta _ ->
    let dist = DBeta {a = mulf_ driftScale x, b = mulf_ driftScale (subf_ (float_ 1.) x)} in
    Some (dist_ dist)

  -- exp = x, var = x*drift/x+drift --
  | DBinomial _ ->
    let pBody = subf_ (float_ 1.0) (divf_ driftScale (addf_ (int2float_ x) driftScale)) in
    let pName = nameSym "p" in
    let p = nvar_ pName in
    Some (bind_ (nulet_ pName pBody) (dist_ (DBinomial {n = ceilfi_ (divf_ (int2float_ x) p), p = p})))

  | DBernoulli _ ->
    let pBody = if_ x (float_ 0.) (float_ 1.) in
    let pName = nameSym "p" in
    let p = nvar_ pName in
    Some (bind_ (nulet_ pName pBody) (dist_ (DBernoulli {p = p})))

  -- exp_i = x_i/sum(x),  var_i = x_i*(sum(x) - x_i)/(drift*sum(x)*(sum(x)+1)) --
  | DDirichlet _ ->
    Some (dist_ (DDirichlet {a = map_ (ulam_ "x" (mulf_ driftScale (var_ "x"))) x}))

  -- exp = x, var = 0 --
  | DExponential _ ->
    Some (dist_ (DUniform {a = divf_ x driftScale, b = mulf_ x driftScale}))

  -- exp = x,  var = x*drift --
  | DGamma _ ->
    Some (dist_ (DGamma {k = divf_ x driftScale, theta = driftScale}))

  -- exp = x, var = drift -
  | DGaussian _ ->
    Some (dist_ (DGaussian {mu = x, sigma = driftScale}))

  -- exp = x, var = x*drift/x+drift --
  | DGeometric _ ->
    let pBody = subf_ (float_ 1.0) (divf_ driftScale (addf_ (int2float_ x) driftScale)) in
    let pName = nameSym "p" in
    let p = nvar_ pName in
    Some (bind_ (nulet_ pName pBody) (dist_ (DBinomial {n = ceilfi_ (divf_ (int2float_ x) p), p = p})))

  -- WARNING : if (x > drift) => p > 1 AND if drift < 1 => n <1 --
  -- exp_i = x_i,  var_i = x_i (1 - x_i/drift_1)
  -- | DMultinomial _ ->
  --  Some (dist_ (DMultinomial {n = ceilfi_ driftScale, p = map_ (ulam_ "x" (divf_ (var_ "x") (ceilfi_ driftScale))) (map_ (ulam_ "x" (int2float_ (var_ "x"))) x)}))

  -- exp = x, var = x*drift/x+drift --
  | DNegBinomial _ ->
    let pBody = subf_ (float_ 1.0) (divf_ driftScale (addf_ (int2float_ x) driftScale)) in
    let pName = nameSym "p" in
    let p = nvar_ pName in
    Some (bind_ (nulet_ pName pBody) (dist_ (DNegBinomial {n = ceilfi_ (divf_ (int2float_ x) p), p = p})))

  -- exp = x, var = x*drift/x+drift --
  | DPoisson _ ->
    let pBody = subf_ (float_ 1.0) (divf_ driftScale (addf_ (int2float_ x) driftScale)) in
    let pName = nameSym "p" in
    let p = nvar_ pName in
    Some (bind_ (nulet_ pName pBody) (dist_ (DBinomial {n = ceilfi_ (divf_ (int2float_ x) p), p = p})))

  | DUniform _ ->
    Some (dist_ (DUniform {a = subf_ x driftScale, b = addf_ x driftScale}))
end