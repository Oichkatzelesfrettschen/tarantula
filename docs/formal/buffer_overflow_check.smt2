; Z3 SMT-LIB2 Model for Buffer Allocation Safety
; Verifies no integer overflow in buffer size calculations

; Declare constants for buffer allocation
(declare-const elem_size (_ BitVec 32))
(declare-const elem_count (_ BitVec 32))
(declare-const total_size (_ BitVec 32))
(declare-const max_size (_ BitVec 32))

; Define the allocation computation
(assert (= total_size (bvmul elem_size elem_count)))

; Define maximum allocatable size (e.g., 1GB = 2^30)
(assert (= max_size (_ bv1073741824 32)))  ; 1GB limit

; Constraints on inputs (reasonable values)
(assert (bvugt elem_size (_ bv0 32)))  ; Element size must be positive
(assert (bvugt elem_count (_ bv0 32))) ; Count must be positive

; Check for overflow conditions
(define-fun has_overflow () Bool
  (or
    ; Overflow if result smaller than either operand
    (bvult total_size elem_size)
    (bvult total_size elem_count)
    ; Overflow if exceeds maximum
    (bvugt total_size max_size)
  )
)

; Assertion: Check if overflow is satisfiable
; If SAT, there exists input that causes overflow
; If UNSAT, no overflow possible for constrained inputs
(assert has_overflow)

(check-sat)
(get-model)

; Additional checks for specific scenarios
(push)
(echo "Checking large element size...")
(assert (= elem_size (_ bv1048576 32)))  ; 1MB elements
(assert (= elem_count (_ bv1024 32)))    ; 1024 elements
(check-sat)
(pop)

(push)
(echo "Checking maximum safe allocation...")
(assert (= elem_size (_ bv1 32)))
(assert (= elem_count (_ bv1073741824 32)))  ; 1GB of 1-byte elements
(check-sat)
(pop)

(push)
(echo "Checking overflow scenario...")
(assert (= elem_size (_ bv65536 32)))    ; 64KB elements
(assert (= elem_count (_ bv100000 32)))  ; 100k elements = 6.4GB
(check-sat)
(pop)
