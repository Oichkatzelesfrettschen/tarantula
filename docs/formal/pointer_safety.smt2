; Z3 Model for Pointer Arithmetic Safety
; Verifies pointer bounds checking and alignment

; Declare pointer and offset types
(declare-const base_ptr (_ BitVec 64))
(declare-const offset (_ BitVec 64))
(declare-const result_ptr (_ BitVec 64))
(declare-const buf_size (_ BitVec 64))

; Pointer arithmetic: result = base + offset
(assert (= result_ptr (bvadd base_ptr offset)))

; Define valid buffer region
(declare-const buf_start (_ BitVec 64))
(declare-const buf_end (_ BitVec 64))
(assert (= buf_end (bvadd buf_start buf_size)))

; Base pointer must be within buffer
(assert (bvuge base_ptr buf_start))
(assert (bvult base_ptr buf_end))

; Check for pointer overflow
(define-fun ptr_overflow () Bool
  (bvult result_ptr base_ptr)  ; Wrapped around
)

; Check for out-of-bounds access
(define-fun out_of_bounds () Bool
  (or
    (bvult result_ptr buf_start)
    (bvuge result_ptr buf_end)
  )
)

; Alignment check (8-byte aligned for 64-bit pointers)
(define-fun misaligned () Bool
  (not (= (bvand result_ptr (_ bv7 64)) (_ bv0 64)))
)

; Combined safety violation
(define-fun unsafe () Bool
  (or ptr_overflow out_of_bounds misaligned)
)

; Assert that unsafe condition is reachable
(assert unsafe)

(check-sat)
(get-model)

; Test specific scenarios
(push)
(echo "Checking normal forward pointer arithmetic...")
(assert (= buf_start (_ bv4096 64)))
(assert (= buf_size (_ bv1024 64)))
(assert (= base_ptr (_ bv4096 64)))
(assert (= offset (_ bv512 64)))
(check-sat)  ; Should be UNSAT (safe)
(pop)

(push)
(echo "Checking overflow scenario...")
(assert (= base_ptr #xfffffffffff000))
(assert (= offset #x0000000000002000))
(check-sat)  ; Should be SAT (unsafe - overflow)
(pop)

(push)
(echo "Checking out-of-bounds...")
(assert (= buf_start (_ bv4096 64)))
(assert (= buf_size (_ bv1024 64)))
(assert (= base_ptr (_ bv4096 64)))
(assert (= offset (_ bv2048 64)))  ; Goes past buffer end
(check-sat)  ; Should be SAT (unsafe - OOB)
(pop)
