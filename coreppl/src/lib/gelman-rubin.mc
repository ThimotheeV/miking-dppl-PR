include "string.mc"
include "common.mc"
include "stats.mc"

type GDRstate = {
  b: Int,
  samples: [Float],
  delta: Float,
  iter: Int,
  bLocalMean: ([Float],[Float]),
  ssd: Float
}

type SampleInfo =
  { weight : Float
  , priorWeight : Float
  }

-- -------- Calculation Revisited Gelman Rubin Diagnostic (see Vats et Knudson, 2020) -------------

let gloMean : [Float] -> Float = 
  lam vec.
    let sum = foldl addf 0. vec in
    divf sum (int2float (length vec))

utest length [1.,2.,3.,4.,5.] with 5
utest gloMean [1.,2.,3.,4.,5.] with 3.

let var : [Float] -> Float -> Float = 
  lam vec. lam mean.
  let nf = int2float (length vec) in 
  mulf (divf 1. (subf nf 1.)) (foldl addf 0. (map (lam x. (pow (subf x mean) 2.)) vec))

utest (var [2.,2.,2.,2.,2.,2.,2.,3.,5.,2.,4.,3.,4.,5.,5.] 3.) with (divf 22. 14.) using eqfApprox 0.001

-- Welford's algorithm + Chan et al. (1976) (ssd = sum of squares of differences)
let update_ssd : [Float] -> Int -> Float -> Float -> Float = 
  lam vec. lam old_size. lam old_mean. lam old_ssd.
  let old_size = int2float old_size in
  let vec_size = int2float (length vec) in
  let vec_mean = gloMean vec in
  let cumul_size = addf vec_size old_size in
  let delta = subf vec_mean old_mean in
  let update_mean = addf old_mean (mulf delta (divf vec_size cumul_size)) in
  let vec_ssd = foldl addf 0. (map (lam x. (pow (subf x vec_mean) 2.)) vec) in
  addf old_ssd (addf vec_ssd (mulf (pow delta 2.) (divf (mulf vec_size old_size) cumul_size)))

utest (var [2.,2.,2.,2.,2.,2.,2.,3.,5.,2.] 2.4) with 0.933 using eqfApprox 0.001
utest (update_ssd [4.,3.,4.,5.,5.] 10 2.4 8.4) with 22. using eqfApprox 0.001

recursive
let locMean : [Float] -> [Float] -> Int -> [Float] = 
  lam vec. lam loc. lam b.
    if eqi (length vec) 0 then
      reverse loc
    else
      let splt = splitAt vec b in
      let loc = cons (gloMean splt.0) loc in
      locMean splt.1 loc b
end

utest (locMean [1.,1.,1.,1.,1.,1.,2.,3.,4.,5.,2.,3.,4.,5.,6.] [] 5) with [1.,3.,4.]

let changeScale : [Float] -> ([Float] ,[Float]) =
  lam mean.
    let mean1 = locMean mean [] 3 in
    (mean1, mean)

utest (changeScale [4.,3.,2.,5.,4.,3.,3.,2.,1.]) with ([3.,4.,2.], [4.,3.,2.,5.,4.,3.,3.,2.,1.])

let updateChunk : [Float] -> ([Float],[Float]) -> Int -> ([Float] ,[Float]) = 
  lam chunk. lam mean. lam b.
      let mean1 = gloMean chunk in
      let mean3 = locMean chunk [] (divi b 3) in
      (cons mean1 mean.0, concat mean3 mean.1)

utest (updateChunk [4.,3.,2.,5.,4.,3.,3.,2.,1.,4.,3.,2.,5.,4.,3.,3.,2.,1.,4.,3.,2.,5.,4.,3.,3.,2.,1.] ([1.],[1.,1.,1.]) 9) 
  with ([3.,1.], [3.,4.,2.,3.,4.,2.,3.,4.,2.,1.,1.,1.])

let theta : [Float] -> Int -> Int -> Float -> Float = 
  lam locMean. lam a. lam b. lam gloMean.
  let af = int2float a in
  let bf = int2float b in
  mulf (divf bf (subf af 1.)) (foldl addf 0. (map (lam x. (pow (subf x gloMean) 2.)) locMean))

let calcTheta : ([Float],[Float]) -> Float -> Int -> Int -> Float =
  lam locMean. lam mean. lam a. lam b.
    let thetaB = theta locMean.0 a b mean in
    let b3 = divi b 3 in
    let thetaB3 = theta locMean.1 a b3 mean in
    subf (mulf 2. thetaB) thetaB3

let calcPSRF : Float -> Float -> Int -> Float =
  lam theta. lam s. lam n.
    let nf = int2float n in
    let sigma = addf (mulf (divf (subf nf 1.) nf) s) (divf theta nf) in
    sqrt (divf sigma s) 

-- Gamma function => use Spouge’s approximation, "which is fairly efficient but nonoptimal for asymptotically large arguments" Fredrik Johansson
-- for p/2 = 0.5
let gammaFunction : Float -> Float = lam p. 1.772454
-- for p = 1 and quantile = 0.95
let chiSqrtQuant : Float -> Float = lam p. 3.841459

let calcDelta : Float -> Float -> Float = lam m. lam e. 
  let majM = mulf (divf 12.56 (pow (gammaFunction 1.) 2.)) (divf (chiSqrtQuant 1.) (pow e 2.)) in
  sqrt (addf 1. (divf m majM))

utest (calcDelta 3. 0.1) with 1.000976 using eqfApprox 1e-5

let gdr : all a. (a -> Float) -> Int -> GDRstate -> SampleInfo -> a -> (GDRstate, Bool) = 
  lam toFloat. lam burn. lam state. lam sampInf. lam sample.
    let sample = toFloat sample in
    let chunk = cons sample state.samples in
    if eqi (modi state.iter state.b) 0 then
      let bLocalMean = (updateChunk chunk state.bLocalMean state.b) in
      let sumSqrDiff = update_ssd chunk (subi state.iter state.b) (gloMean bLocalMean.0) state.ssd in
      let chunk = [] in
      let state : GDRstate = 
        if (eqi (modi state.iter (muli state.b 9)) 0) then 
          {b = (muli state.b 3), samples = chunk, delta = state.delta, iter = state.iter, bLocalMean = (changeScale bLocalMean.0), ssd = sumSqrDiff}
        else
          {b = state.b, samples = chunk, delta = state.delta, iter = state.iter, bLocalMean = bLocalMean, ssd = sumSqrDiff}
      in
      if (lti state.iter burn) then 
        ({b = state.b, samples = chunk, delta = state.delta, iter = (addi state.iter 1), bLocalMean = state.bLocalMean, ssd = sumSqrDiff}, true)
      else
        let a = divi state.iter state.b in
        let s = divf sumSqrDiff (int2float (subi state.iter 1)) in
        let theta = calcTheta state.bLocalMean (gloMean bLocalMean.0) a state.b in
        let r = calcPSRF theta s state.iter in
        ({b = state.b, samples = chunk, delta = state.delta, iter = (addi state.iter 1), bLocalMean = state.bLocalMean, ssd = sumSqrDiff}, (gtf r state.delta))
    else
      ({b = state.b, samples = chunk, delta = state.delta, iter = (addi state.iter 1), bLocalMean = state.bLocalMean, ssd = state.ssd}, true)
