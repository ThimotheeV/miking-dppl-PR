include "../../../models/diff/regression.mc"
include "../../cppl-test.mc"
include "../../test.mc"

include "seq.mc"
include "sys.mc"
include "string.mc"
include "common.mc"
include "stats.mc"
include "coreppl::lib/gelman-rubin.mc"

mexpr

let s = 1e-1 in
let e = eqDiffReg s in
let rhs = diffRegTruth in
let r = resDiffReg in
let c = cpplResOfDist float2string in

--let initGDRstate : GDRstate = {
--  b = 300,
--  samples = [],
--  delta = (calcDelta 1. 0.05),
--  iter = 1,
--  bLocalMean = ([],[]),
--  ssd = 0.0
--} in

utest r (c 0   (infer (Default {}) model))                                              with rhs using e in
utest r (c 0   (infer (Importance { particles = 1000 }) model))                         with rhs using e in
utest r (c 0   (infer (BPF { particles = 1000 }) model))                                with rhs using e in
utest r (c 0   (infer (APF { particles = 1000 }) model))                                with rhs using e in
utest r (c 500 (infer (PIMH { particles = 10, iterations = 100 }) model))               with rhs using e in
utest r (c 500 (infer (TraceMCMC { iterations = 1000 }) model))                         with rhs using e in
utest r (c 500 (infer (NaiveMCMC { iterations = 1000 }) model))                         with rhs using e in
utest r (c 500 (infer (LightweightMCMC { continue = (lam. 1000, lam x. lam. lam. (subi x 1, geqi x 0)), globalProb = lam. 0.1 }) model)) with rhs using e in
-- utest r (c 500 (infer (LightweightMCMC { continue = (lam. initGDRstate, gdr (lam x. x) 600), globalProb = lam. 0.1 }) model)) with rhs using e in

()
