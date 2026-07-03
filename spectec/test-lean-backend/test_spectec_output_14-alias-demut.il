
;; test.spectec:7.1-7.27
syntax N = nat

;; test.spectec:8.1-8.27
syntax M = nat

;; test.spectec:9.1-9.27
syntax n = nat

;; test.spectec:10.1-10.27
syntax m = nat

;; test.spectec:15.1-15.14
def $Ki : nat
  ;; test.spectec:16.1-16.15
  def $Ki = 1024

;; test.spectec:21.1-21.25
def $min(nat : nat, nat : nat) : nat
  ;; test.spectec:22.1-22.36
  def $min{i : nat, j : nat}(i, j) = (if (i <= j) then i else j)

;; test.spectec:25.1-25.21
rec {

;; test.spectec:25.6-25.10
relation fun_sum: `%%`(nat*, nat)
  ;; test.spectec:25.6-25.10
  rule fun_sum_case_0:
    `%%`([], 0)

  ;; test.spectec:25.6-25.10
  rule fun_sum_case_1{n : nat, `n'*` : n*, var_0 : nat}:
    `%%`([n] ++ n'#1*{n'#1 <- `n'*`}, (n + var_0))
    -- fun_sum: `%%`(n'*{n' <- `n'*`}, var_0)
}

;; test.spectec:32.1-32.58
def $opt_(syntax X, X*) : X??
  ;; test.spectec:33.1-33.31
  def $opt_{syntax X}(syntax X, []) = ?(?())
  ;; test.spectec:34.1-34.27
  def $opt_{syntax X, w : X}(syntax X, [w]) = ?(?(w))
  def $opt_{syntax X, x1 : X*}(syntax X, x1) = ?()
    -- otherwise

;; test.spectec:36.1-36.45
def $list_(syntax X, X?) : X*
  ;; test.spectec:37.1-37.32
  def $list_{syntax X}(syntax X, ?()) = []
  ;; test.spectec:38.1-38.28
  def $list_{syntax X, w : X}(syntax X, ?(w)) = [w]

;; test.spectec:40.1-40.59
rec {

;; test.spectec:40.1-40.59
def $concat_(syntax X, X**) : X*
  ;; test.spectec:41.1-41.34
  def $concat_{syntax X}(syntax X, []) = []
  ;; test.spectec:42.1-42.61
  def $concat_{syntax X, `w*` : X*, `w'**` : X**}(syntax X, [w#1*{w#1 <- `w*`}] ++ w'#1*{w'#1 <- `w'*#1`}*{`w'*#1` <- `w'**`}) = w*{w <- `w*`} ++ $concat_(syntax X, w'*{w' <- `w'*`}*{`w'*` <- `w'**`})
}

;; test.spectec:48.1-48.28
relation Nat_ok: `%|-%`(nat, nat)
  ;; test.spectec:49.1-50.9
  rule refl{n : n}:
    `%|-%`(n, n)

;; test.spectec:52.1-52.31
relation Nats_ok: `%|-%`(nat*, nat*)
  ;; test.spectec:53.1-55.25
  rule all{`n*` : n*}:
    `%|-%`(n*{n <- `n*`}, n*{n <- `n*`})
    -- (Nat_ok: `%|-%`(n, n))*{n <- `n*`}

;; test.spectec:61.1-61.29
relation Pair_ok: `%|-%`(nat, nat)
  ;; test.spectec:62.1-63.9
  rule eq{n : n}:
    `%|-%`(n, n)

;; test.spectec:65.1-65.32
relation Pairs_ok: `%|-%`(nat*, nat*)
  ;; test.spectec:66.1-68.26
  rule all{`n*` : n*, `m*` : m*}:
    `%|-%`(n*{n <- `n*`}, m*{m <- `m*`})
    -- if (|`m*`| = |`n*`|)
    -- (Pair_ok: `%|-%`(n, m))*{m <- `m*`, n <- `n*`}

