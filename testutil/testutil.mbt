// 測試共享工具：把原本四份重複嘅測試 helper 收斂到一處
//（det_rand ×4、prop_ring ×3、prop_elem ×2、is_zero_vec ×2 —— 全部合併）。

///|
/// 確定性偽隨機 ∈ [0, 99991)（乘法同餘；結果經 mod_pos 規範化）。
pub fn det_rand(seed : Int32, salt : Int32) -> Int32 {
  let a = @num.mod_pos(seed, 99991)
  let b = @num.mod_pos(salt, 99991)
  @num.mod_pos(a * 7919 + b * 104729 + 17, 99991)
}

///|
/// 隨機元係數域商環 `𝔽_p[x]/(f)`：`ps` = 域素數候選（finite 用 [2,3,5]、
/// modules/scheme 用 [2,3]）；首項係數取單位，`deg f ∈ 1..2`。
pub fn prop_ring(seed : Int32, ps : Array[Int32]) -> @finite.FinAlg {
  let s = @num.mod_pos(seed, 100000)
  let p = ps[@num.mod_pos(det_rand(s, 1), ps.length())]
  let d = 1 + @num.mod_pos(det_rand(s, 2), 2)
  let coeffs : Array[Int32] = []
  for i in 0..<(d + 1) {
    coeffs.push(@num.mod_pos(det_rand(s, 10 + i), p))
  }
  coeffs[d] = 1 + @num.mod_pos(det_rand(s, 20), p - 1) // 單位首項係數
  @finite.FinAlg::univariate_quotient(p, coeffs)
}

///|
/// 隨機元素（`d` 維座標，逐位 mod p）。
pub fn prop_elem(
  seed : Int32,
  salt : Int32,
  p : Int32,
  d : Int32,
) -> Array[Int32] {
  let out : Array[Int32] = []
  for j in 0..<d {
    out.push(@num.mod_pos(det_rand(seed, 30 + salt * 10 + j), p))
  }
  out
}

///|
/// 零向量判定。
pub fn is_zero_vec(v : Array[Int32]) -> Bool {
  for x in v {
    if x != 0 {
      return false
    }
  }
  true
}
