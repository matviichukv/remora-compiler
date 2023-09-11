open! Base
open Remora

let%expect_test "check simplifying" =
  let pipeline =
    CompilerPipeline.(
      (module Parse.Stage (Source.UnitBuilder))
      @> (module TypeCheckStage.M (Source.UnitBuilder))
      @> (module Explicitize.Stage (Source.UnitBuilder))
      @> (module Inline.Stage (Source.UnitBuilder))
      @> (module Simplify.Stage (Source.UnitBuilder))
      @> (module Show.Stage (Nucleus) (Source.UnitBuilder))
      @> empty)
  in
  let checkAndPrint = TestPipeline.runAndPrint pipeline in
  checkAndPrint {| 5 |};
  [%expect
    {|
    (Scalar
     ((element (Literal (IntLiteral 5)))
      (type' ((element (Literal IntLiteral)) (shape ()))))) |}];
  checkAndPrint {| (+ 1 2) |};
  [%expect
    {|
    (Scalar
     ((element (Literal (IntLiteral 3)))
      (type' ((element (Literal IntLiteral)) (shape ()))))) |}];
  checkAndPrint {| (+ [1 2 3] 4) |};
  [%expect
    {|
    (IntrinsicCall
     (Map (frameShape ((Add ((const 3) (refs ())))))
      (args
       (((binding ((name +arg1) (id 26)))
         (value
          (Frame
           ((dimensions (3))
            (elements
             ((Scalar
               ((element (Literal (IntLiteral 1)))
                (type' ((element (Literal IntLiteral)) (shape ())))))
              (Scalar
               ((element (Literal (IntLiteral 2)))
                (type' ((element (Literal IntLiteral)) (shape ())))))
              (Scalar
               ((element (Literal (IntLiteral 3)))
                (type' ((element (Literal IntLiteral)) (shape ())))))))
            (type'
             ((element (Literal IntLiteral))
              (shape ((Add ((const 3) (refs ())))))))))))))
      (body
       (PrimitiveCall
        ((op Add)
         (args
          ((Ref
            ((id ((name +arg1) (id 26)))
             (type' ((element (Literal IntLiteral)) (shape ())))))
           (Scalar
            ((element (Literal (IntLiteral 4)))
             (type' ((element (Literal IntLiteral)) (shape ())))))))
         (type' ((element (Literal IntLiteral)) (shape ()))))))
      (type'
       ((element (Literal IntLiteral)) (shape ((Add ((const 3) (refs ()))))))))) |}];
  checkAndPrint {|
    (t-fn (@t) "hello"){int| }
  |};
  [%expect
    {|
    (Frame
     ((dimensions (5))
      (elements
       ((Scalar
         ((element (Literal (CharacterLiteral h)))
          (type' ((element (Literal CharacterLiteral)) (shape ())))))
        (Scalar
         ((element (Literal (CharacterLiteral e)))
          (type' ((element (Literal CharacterLiteral)) (shape ())))))
        (Scalar
         ((element (Literal (CharacterLiteral l)))
          (type' ((element (Literal CharacterLiteral)) (shape ())))))
        (Scalar
         ((element (Literal (CharacterLiteral l)))
          (type' ((element (Literal CharacterLiteral)) (shape ())))))
        (Scalar
         ((element (Literal (CharacterLiteral o)))
          (type' ((element (Literal CharacterLiteral)) (shape ())))))))
      (type'
       ((element (Literal CharacterLiteral))
        (shape ((Add ((const 5) (refs ()))))))))) |}];
  checkAndPrint {|
    (define (id{@t| } [x @t]) x)
    (id{int| } 5)
  |};
  [%expect
    {|
    (Scalar
     ((element (Literal (IntLiteral 5)))
      (type' ((element (Literal IntLiteral)) (shape ()))))) |}];
  checkAndPrint
    {|
      (define id (t-fn (@t) (fn ([x @t]) x)))
      (id{(Forall (@t) (-> (@t) @t))| } id)
    |};
  [%expect
    {|
    (Scalar
     ((element (Literal UnitLiteral))
      (type' ((element (Literal UnitLiteral)) (shape ()))))) |}];
  checkAndPrint
    {|
      (define id (t-fn (@t) (fn ([x @t]) x)))
      ((t-app (id{(Forall (@t) (-> (@t) @t))| } id) int) 5)
    |};
  [%expect
    {|
    (Scalar
     ((element (Literal (IntLiteral 5)))
      (type' ((element (Literal IntLiteral)) (shape ()))))) |}];
  checkAndPrint
    {|
      ((t-app (t-app (t-fn (@a) (t-fn (@b) (fn ([x int]) x))) int) int) 10)
    |};
  [%expect
    {|
    (Scalar
     ((element (Literal (IntLiteral 10)))
      (type' ((element (Literal IntLiteral)) (shape ()))))) |}];
  checkAndPrint {|
      (length{int | 5 []} [1 2 3 4 5])
    |};
  [%expect
    {|
    (Scalar
     ((element (Literal (IntLiteral 5)))
      (type' ((element (Literal IntLiteral)) (shape ()))))) |}];
  checkAndPrint {| 
    (reduce{int | 4 [] []} + [1 2 3 4 5])
  |};
  [%expect
    {|
    (IntrinsicCall
     (Reduce
      (args
       (((firstBinding ((name reduceArg1) (id 28)))
         (secondBinding ((name reduceArg2) (id 29)))
         (value
          (Frame
           ((dimensions (5))
            (elements
             ((Scalar
               ((element (Literal (IntLiteral 1)))
                (type' ((element (Literal IntLiteral)) (shape ())))))
              (Scalar
               ((element (Literal (IntLiteral 2)))
                (type' ((element (Literal IntLiteral)) (shape ())))))
              (Scalar
               ((element (Literal (IntLiteral 3)))
                (type' ((element (Literal IntLiteral)) (shape ())))))
              (Scalar
               ((element (Literal (IntLiteral 4)))
                (type' ((element (Literal IntLiteral)) (shape ())))))
              (Scalar
               ((element (Literal (IntLiteral 5)))
                (type' ((element (Literal IntLiteral)) (shape ())))))))
            (type'
             ((element (Literal IntLiteral))
              (shape ((Add ((const 5) (refs ())))))))))))))
      (body
       (PrimitiveCall
        ((op Add)
         (args
          ((Ref
            ((id ((name reduceArg1) (id 28)))
             (type' ((element (Literal IntLiteral)) (shape ())))))
           (Ref
            ((id ((name reduceArg2) (id 29)))
             (type' ((element (Literal IntLiteral)) (shape ())))))))
         (type' ((element (Literal IntLiteral)) (shape ()))))))
      (t (Literal IntLiteral)) (dSub1 ((const 4) (refs ()))) (itemPad ())
      (cellShape ()) (type' ((element (Literal IntLiteral)) (shape ()))))) |}];
  checkAndPrint
    {|
      (define (id{@t| } [x @t]) x)
      ((t-app [id id id] int) 5)
    |};
  [%expect
    {|
    (IntrinsicCall
     (Map (frameShape ((Add ((const 3) (refs ()))))) (args ())
      (body
       (Scalar
        ((element (Literal (IntLiteral 5)))
         (type' ((element (Literal IntLiteral)) (shape ()))))))
      (type'
       ((element (Literal IntLiteral)) (shape ((Add ((const 3) (refs ()))))))))) |}];
  checkAndPrint
    {|
      (define (id{@t| } [x @t]) x)
      (+
        (length{int | 5 []} [1 2 3 4 5])
        (length{char | 2 [2]} ["hi" "ih"]))
    |};
  [%expect
    {|
    (Scalar
     ((element (Literal (IntLiteral 7)))
      (type' ((element (Literal IntLiteral)) (shape ()))))) |}];
  checkAndPrint
    {|
      (t-app
        (reduce{(Forall (@t) int) | 1 [] []}
          (fn ([a (Forall (@a) int)] [b (Forall (@b) int)])
            (define sum (+ (t-app a char) (t-app b int)))
            (t-fn (@u) sum))
          [(t-fn (@x) 1) (t-fn (@y) 2)])
        int)
    |};
  [%expect
    {|
    (IntrinsicCall
     (Reduce
      (args
       (((firstBinding ((name reduce-arg1) (id 49)))
         (secondBinding ((name reduceArg2) (id 46)))
         (value
          (Frame
           ((dimensions (2))
            (elements
             ((Scalar
               ((element (Literal (IntLiteral 1)))
                (type' ((element (Literal IntLiteral)) (shape ())))))
              (Scalar
               ((element (Literal (IntLiteral 2)))
                (type' ((element (Literal IntLiteral)) (shape ())))))))
            (type'
             ((element (Literal IntLiteral))
              (shape ((Add ((const 2) (refs ())))))))))))
        ((firstBinding ((name reduceArg1) (id 43)))
         (secondBinding ((name reduce-arg2) (id 50)))
         (value
          (Frame
           ((dimensions (2))
            (elements
             ((Scalar
               ((element (Literal (IntLiteral 1)))
                (type' ((element (Literal IntLiteral)) (shape ())))))
              (Scalar
               ((element (Literal (IntLiteral 2)))
                (type' ((element (Literal IntLiteral)) (shape ())))))))
            (type'
             ((element (Literal IntLiteral))
              (shape ((Add ((const 2) (refs ())))))))))))))
      (body
       (PrimitiveCall
        ((op Add)
         (args
          ((Ref
            ((id ((name reduceArg1) (id 43)))
             (type' ((element (Literal IntLiteral)) (shape ())))))
           (Ref
            ((id ((name reduceArg2) (id 46)))
             (type' ((element (Literal IntLiteral)) (shape ())))))))
         (type' ((element (Literal IntLiteral)) (shape ()))))))
      (t (Literal IntLiteral)) (dSub1 ((const 1) (refs ()))) (itemPad ())
      (cellShape ()) (type' ((element (Literal IntLiteral)) (shape ()))))) |}];
  checkAndPrint
    {|
      (define (foo [x int])
        (define y (+ [1 2 3] 4))
        (+ x (+ y y)))
      (foo [5 6 7])
    |};
  [%expect
    {|
    (IntrinsicCall
     (Map (frameShape ())
      (args
       (((binding ((name y) (id 51)))
         (value
          (IntrinsicCall
           (Map (frameShape ((Add ((const 3) (refs ())))))
            (args
             (((binding ((name +arg1) (id 49)))
               (value
                (Frame
                 ((dimensions (3))
                  (elements
                   ((Scalar
                     ((element (Literal (IntLiteral 1)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))
                    (Scalar
                     ((element (Literal (IntLiteral 2)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))
                    (Scalar
                     ((element (Literal (IntLiteral 3)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))))
                  (type'
                   ((element (Literal IntLiteral))
                    (shape ((Add ((const 3) (refs ())))))))))))))
            (body
             (PrimitiveCall
              ((op Add)
               (args
                ((Ref
                  ((id ((name +arg1) (id 49)))
                   (type' ((element (Literal IntLiteral)) (shape ())))))
                 (Scalar
                  ((element (Literal (IntLiteral 4)))
                   (type' ((element (Literal IntLiteral)) (shape ())))))))
               (type' ((element (Literal IntLiteral)) (shape ()))))))
            (type'
             ((element (Literal IntLiteral))
              (shape ((Add ((const 3) (refs ())))))))))))))
      (body
       (IntrinsicCall
        (Map (frameShape ())
         (args
          (((binding ((name hoistedExp) (id 58)))
            (value
             (IntrinsicCall
              (Map (frameShape ((Add ((const 3) (refs ())))))
               (args
                (((binding ((name +arg1) (id 53)))
                  (value
                   (Ref
                    ((id ((name y) (id 51)))
                     (type'
                      ((element (Literal IntLiteral))
                       (shape ((Add ((const 3) (refs ())))))))))))
                 ((binding ((name +arg2) (id 55)))
                  (value
                   (Ref
                    ((id ((name y) (id 51)))
                     (type'
                      ((element (Literal IntLiteral))
                       (shape ((Add ((const 3) (refs ())))))))))))))
               (body
                (PrimitiveCall
                 ((op Add)
                  (args
                   ((Ref
                     ((id ((name +arg1) (id 53)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))
                    (Ref
                     ((id ((name +arg2) (id 55)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))))
                  (type' ((element (Literal IntLiteral)) (shape ()))))))
               (type'
                ((element (Literal IntLiteral))
                 (shape ((Add ((const 3) (refs ())))))))))))))
         (body
          (IntrinsicCall
           (Map (frameShape ((Add ((const 3) (refs ())))))
            (args
             (((binding ((name x) (id 44)))
               (value
                (Frame
                 ((dimensions (3))
                  (elements
                   ((Scalar
                     ((element (Literal (IntLiteral 5)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))
                    (Scalar
                     ((element (Literal (IntLiteral 6)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))
                    (Scalar
                     ((element (Literal (IntLiteral 7)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))))
                  (type'
                   ((element (Literal IntLiteral))
                    (shape ((Add ((const 3) (refs ())))))))))))))
            (body
             (IntrinsicCall
              (Map (frameShape ((Add ((const 3) (refs ())))))
               (args
                (((binding ((name +arg2) (id 57)))
                  (value
                   (Ref
                    ((id ((name hoistedExp) (id 58)))
                     (type'
                      ((element (Literal IntLiteral))
                       (shape ((Add ((const 3) (refs ())))))))))))))
               (body
                (PrimitiveCall
                 ((op Add)
                  (args
                   ((Ref
                     ((id ((name x) (id 44)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))
                    (Ref
                     ((id ((name +arg2) (id 57)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))))
                  (type' ((element (Literal IntLiteral)) (shape ()))))))
               (type'
                ((element (Literal IntLiteral))
                 (shape ((Add ((const 3) (refs ()))))))))))
            (type'
             ((element (Literal IntLiteral))
              (shape ((Add ((const 3) (refs ()))) (Add ((const 3) (refs ()))))))))))
         (type'
          ((element (Literal IntLiteral))
           (shape ((Add ((const 3) (refs ()))) (Add ((const 3) (refs ()))))))))))
      (type'
       ((element (Literal IntLiteral))
        (shape ((Add ((const 3) (refs ()))) (Add ((const 3) (refs ()))))))))) |}];
  checkAndPrint
    {|
      (define (foo [x int])
        (define y (+ [1 2 3] 4))
        (+ x y))
      (foo [5 6 7])
    |};
  [%expect
    {|
    (IntrinsicCall
     (Map (frameShape ())
      (args
       (((binding ((name hoistedExp) (id 48)))
         (value
          (IntrinsicCall
           (Map (frameShape ((Add ((const 3) (refs ())))))
            (args
             (((binding ((name +arg1) (id 43)))
               (value
                (Frame
                 ((dimensions (3))
                  (elements
                   ((Scalar
                     ((element (Literal (IntLiteral 1)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))
                    (Scalar
                     ((element (Literal (IntLiteral 2)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))
                    (Scalar
                     ((element (Literal (IntLiteral 3)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))))
                  (type'
                   ((element (Literal IntLiteral))
                    (shape ((Add ((const 3) (refs ())))))))))))))
            (body
             (PrimitiveCall
              ((op Add)
               (args
                ((Ref
                  ((id ((name +arg1) (id 43)))
                   (type' ((element (Literal IntLiteral)) (shape ())))))
                 (Scalar
                  ((element (Literal (IntLiteral 4)))
                   (type' ((element (Literal IntLiteral)) (shape ())))))))
               (type' ((element (Literal IntLiteral)) (shape ()))))))
            (type'
             ((element (Literal IntLiteral))
              (shape ((Add ((const 3) (refs ())))))))))))))
      (body
       (IntrinsicCall
        (Map (frameShape ((Add ((const 3) (refs ())))))
         (args
          (((binding ((name x) (id 39)))
            (value
             (Frame
              ((dimensions (3))
               (elements
                ((Scalar
                  ((element (Literal (IntLiteral 5)))
                   (type' ((element (Literal IntLiteral)) (shape ())))))
                 (Scalar
                  ((element (Literal (IntLiteral 6)))
                   (type' ((element (Literal IntLiteral)) (shape ())))))
                 (Scalar
                  ((element (Literal (IntLiteral 7)))
                   (type' ((element (Literal IntLiteral)) (shape ())))))))
               (type'
                ((element (Literal IntLiteral))
                 (shape ((Add ((const 3) (refs ())))))))))))))
         (body
          (IntrinsicCall
           (Map (frameShape ((Add ((const 3) (refs ())))))
            (args
             (((binding ((name +arg2) (id 47)))
               (value
                (Ref
                 ((id ((name hoistedExp) (id 48)))
                  (type'
                   ((element (Literal IntLiteral))
                    (shape ((Add ((const 3) (refs ())))))))))))))
            (body
             (PrimitiveCall
              ((op Add)
               (args
                ((Ref
                  ((id ((name x) (id 39)))
                   (type' ((element (Literal IntLiteral)) (shape ())))))
                 (Ref
                  ((id ((name +arg2) (id 47)))
                   (type' ((element (Literal IntLiteral)) (shape ())))))))
               (type' ((element (Literal IntLiteral)) (shape ()))))))
            (type'
             ((element (Literal IntLiteral))
              (shape ((Add ((const 3) (refs ()))))))))))
         (type'
          ((element (Literal IntLiteral))
           (shape ((Add ((const 3) (refs ()))) (Add ((const 3) (refs ()))))))))))
      (type'
       ((element (Literal IntLiteral))
        (shape ((Add ((const 3) (refs ()))) (Add ((const 3) (refs ()))))))))) |}];
  checkAndPrint
    {|
      (define (foo [x int])
        (define y (+ [1 2 3] 4))
        (+ x (+ y y)))
      (foo 5)
    |};
  [%expect
    {|
    (IntrinsicCall
     (Map (frameShape ())
      (args
       (((binding ((name y) (id 49)))
         (value
          (IntrinsicCall
           (Map (frameShape ((Add ((const 3) (refs ())))))
            (args
             (((binding ((name +arg1) (id 47)))
               (value
                (Frame
                 ((dimensions (3))
                  (elements
                   ((Scalar
                     ((element (Literal (IntLiteral 1)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))
                    (Scalar
                     ((element (Literal (IntLiteral 2)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))
                    (Scalar
                     ((element (Literal (IntLiteral 3)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))))
                  (type'
                   ((element (Literal IntLiteral))
                    (shape ((Add ((const 3) (refs ())))))))))))))
            (body
             (PrimitiveCall
              ((op Add)
               (args
                ((Ref
                  ((id ((name +arg1) (id 47)))
                   (type' ((element (Literal IntLiteral)) (shape ())))))
                 (Scalar
                  ((element (Literal (IntLiteral 4)))
                   (type' ((element (Literal IntLiteral)) (shape ())))))))
               (type' ((element (Literal IntLiteral)) (shape ()))))))
            (type'
             ((element (Literal IntLiteral))
              (shape ((Add ((const 3) (refs ())))))))))))))
      (body
       (IntrinsicCall
        (Map (frameShape ((Add ((const 3) (refs ())))))
         (args
          (((binding ((name +arg2) (id 55)))
            (value
             (IntrinsicCall
              (Map (frameShape ((Add ((const 3) (refs ())))))
               (args
                (((binding ((name +arg1) (id 51)))
                  (value
                   (Ref
                    ((id ((name y) (id 49)))
                     (type'
                      ((element (Literal IntLiteral))
                       (shape ((Add ((const 3) (refs ())))))))))))
                 ((binding ((name +arg2) (id 53)))
                  (value
                   (Ref
                    ((id ((name y) (id 49)))
                     (type'
                      ((element (Literal IntLiteral))
                       (shape ((Add ((const 3) (refs ())))))))))))))
               (body
                (PrimitiveCall
                 ((op Add)
                  (args
                   ((Ref
                     ((id ((name +arg1) (id 51)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))
                    (Ref
                     ((id ((name +arg2) (id 53)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))))
                  (type' ((element (Literal IntLiteral)) (shape ()))))))
               (type'
                ((element (Literal IntLiteral))
                 (shape ((Add ((const 3) (refs ())))))))))))))
         (body
          (PrimitiveCall
           ((op Add)
            (args
             ((Scalar
               ((element (Literal (IntLiteral 5)))
                (type' ((element (Literal IntLiteral)) (shape ())))))
              (Ref
               ((id ((name +arg2) (id 55)))
                (type' ((element (Literal IntLiteral)) (shape ())))))))
            (type' ((element (Literal IntLiteral)) (shape ()))))))
         (type'
          ((element (Literal IntLiteral)) (shape ((Add ((const 3) (refs ()))))))))))
      (type'
       ((element (Literal IntLiteral)) (shape ((Add ((const 3) (refs ()))))))))) |}];
  checkAndPrint
    {|
      (define (foo [x int])
        (define y (+ [1 2 3] x))
        (+ x (+ y y)))
      (foo [5 6 7])
    |};
  [%expect
    {|
    (IntrinsicCall
     (Map (frameShape ((Add ((const 3) (refs ())))))
      (args
       (((binding ((name x) (id 44)))
         (value
          (Frame
           ((dimensions (3))
            (elements
             ((Scalar
               ((element (Literal (IntLiteral 5)))
                (type' ((element (Literal IntLiteral)) (shape ())))))
              (Scalar
               ((element (Literal (IntLiteral 6)))
                (type' ((element (Literal IntLiteral)) (shape ())))))
              (Scalar
               ((element (Literal (IntLiteral 7)))
                (type' ((element (Literal IntLiteral)) (shape ())))))))
            (type'
             ((element (Literal IntLiteral))
              (shape ((Add ((const 3) (refs ())))))))))))))
      (body
       (IntrinsicCall
        (Map (frameShape ())
         (args
          (((binding ((name y) (id 51)))
            (value
             (IntrinsicCall
              (Map (frameShape ((Add ((const 3) (refs ())))))
               (args
                (((binding ((name +arg1) (id 49)))
                  (value
                   (Frame
                    ((dimensions (3))
                     (elements
                      ((Scalar
                        ((element (Literal (IntLiteral 1)))
                         (type' ((element (Literal IntLiteral)) (shape ())))))
                       (Scalar
                        ((element (Literal (IntLiteral 2)))
                         (type' ((element (Literal IntLiteral)) (shape ())))))
                       (Scalar
                        ((element (Literal (IntLiteral 3)))
                         (type' ((element (Literal IntLiteral)) (shape ())))))))
                     (type'
                      ((element (Literal IntLiteral))
                       (shape ((Add ((const 3) (refs ())))))))))))))
               (body
                (PrimitiveCall
                 ((op Add)
                  (args
                   ((Ref
                     ((id ((name +arg1) (id 49)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))
                    (Ref
                     ((id ((name x) (id 44)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))))
                  (type' ((element (Literal IntLiteral)) (shape ()))))))
               (type'
                ((element (Literal IntLiteral))
                 (shape ((Add ((const 3) (refs ())))))))))))))
         (body
          (IntrinsicCall
           (Map (frameShape ((Add ((const 3) (refs ())))))
            (args
             (((binding ((name +arg2) (id 57)))
               (value
                (IntrinsicCall
                 (Map (frameShape ((Add ((const 3) (refs ())))))
                  (args
                   (((binding ((name +arg1) (id 53)))
                     (value
                      (Ref
                       ((id ((name y) (id 51)))
                        (type'
                         ((element (Literal IntLiteral))
                          (shape ((Add ((const 3) (refs ())))))))))))
                    ((binding ((name +arg2) (id 55)))
                     (value
                      (Ref
                       ((id ((name y) (id 51)))
                        (type'
                         ((element (Literal IntLiteral))
                          (shape ((Add ((const 3) (refs ())))))))))))))
                  (body
                   (PrimitiveCall
                    ((op Add)
                     (args
                      ((Ref
                        ((id ((name +arg1) (id 53)))
                         (type' ((element (Literal IntLiteral)) (shape ())))))
                       (Ref
                        ((id ((name +arg2) (id 55)))
                         (type' ((element (Literal IntLiteral)) (shape ())))))))
                     (type' ((element (Literal IntLiteral)) (shape ()))))))
                  (type'
                   ((element (Literal IntLiteral))
                    (shape ((Add ((const 3) (refs ())))))))))))))
            (body
             (PrimitiveCall
              ((op Add)
               (args
                ((Ref
                  ((id ((name x) (id 44)))
                   (type' ((element (Literal IntLiteral)) (shape ())))))
                 (Ref
                  ((id ((name +arg2) (id 57)))
                   (type' ((element (Literal IntLiteral)) (shape ())))))))
               (type' ((element (Literal IntLiteral)) (shape ()))))))
            (type'
             ((element (Literal IntLiteral))
              (shape ((Add ((const 3) (refs ()))))))))))
         (type'
          ((element (Literal IntLiteral)) (shape ((Add ((const 3) (refs ()))))))))))
      (type'
       ((element (Literal IntLiteral))
        (shape ((Add ((const 3) (refs ()))) (Add ((const 3) (refs ()))))))))) |}];
  checkAndPrint
    {|
      (define (foo [x int])
        (define y (+ 3 4))
        (+ x (+ y y)))
      (foo [5 6 7])
    |};
  [%expect
    {|
    (IntrinsicCall
     (Map (frameShape ((Add ((const 3) (refs ())))))
      (args
       (((binding ((name x) (id 40)))
         (value
          (Frame
           ((dimensions (3))
            (elements
             ((Scalar
               ((element (Literal (IntLiteral 5)))
                (type' ((element (Literal IntLiteral)) (shape ())))))
              (Scalar
               ((element (Literal (IntLiteral 6)))
                (type' ((element (Literal IntLiteral)) (shape ())))))
              (Scalar
               ((element (Literal (IntLiteral 7)))
                (type' ((element (Literal IntLiteral)) (shape ())))))))
            (type'
             ((element (Literal IntLiteral))
              (shape ((Add ((const 3) (refs ())))))))))))))
      (body
       (PrimitiveCall
        ((op Add)
         (args
          ((Ref
            ((id ((name x) (id 40)))
             (type' ((element (Literal IntLiteral)) (shape ())))))
           (Scalar
            ((element (Literal (IntLiteral 14)))
             (type' ((element (Literal IntLiteral)) (shape ())))))))
         (type' ((element (Literal IntLiteral)) (shape ()))))))
      (type'
       ((element (Literal IntLiteral)) (shape ((Add ((const 3) (refs ()))))))))) |}];
  checkAndPrint {| [[1 2] [3 4] [5 6]] |};
  [%expect
    {|
    (Frame
     ((dimensions (3 2))
      (elements
       ((Scalar
         ((element (Literal (IntLiteral 1)))
          (type' ((element (Literal IntLiteral)) (shape ())))))
        (Scalar
         ((element (Literal (IntLiteral 2)))
          (type' ((element (Literal IntLiteral)) (shape ())))))
        (Scalar
         ((element (Literal (IntLiteral 3)))
          (type' ((element (Literal IntLiteral)) (shape ())))))
        (Scalar
         ((element (Literal (IntLiteral 4)))
          (type' ((element (Literal IntLiteral)) (shape ())))))
        (Scalar
         ((element (Literal (IntLiteral 5)))
          (type' ((element (Literal IntLiteral)) (shape ())))))
        (Scalar
         ((element (Literal (IntLiteral 6)))
          (type' ((element (Literal IntLiteral)) (shape ())))))))
      (type'
       ((element (Literal IntLiteral))
        (shape ((Add ((const 3) (refs ()))) (Add ((const 2) (refs ()))))))))) |}];
  checkAndPrint {| (frame [0] int) |};
  [%expect
    {|
    (Frame
     ((dimensions (0)) (elements ())
      (type'
       ((element (Literal IntLiteral)) (shape ((Add ((const 0) (refs ()))))))))) |}];
  checkAndPrint {| [[1 2] (+ [3 4] [5 6])] |};
  [%expect
    {|
    (Frame
     ((dimensions (2))
      (elements
       ((Frame
         ((dimensions (2))
          (elements
           ((Scalar
             ((element (Literal (IntLiteral 1)))
              (type' ((element (Literal IntLiteral)) (shape ())))))
            (Scalar
             ((element (Literal (IntLiteral 2)))
              (type' ((element (Literal IntLiteral)) (shape ())))))))
          (type'
           ((element (Literal IntLiteral)) (shape ((Add ((const 2) (refs ())))))))))
        (IntrinsicCall
         (Map (frameShape ((Add ((const 2) (refs ())))))
          (args
           (((binding ((name +arg1) (id 27)))
             (value
              (Frame
               ((dimensions (2))
                (elements
                 ((Scalar
                   ((element (Literal (IntLiteral 3)))
                    (type' ((element (Literal IntLiteral)) (shape ())))))
                  (Scalar
                   ((element (Literal (IntLiteral 4)))
                    (type' ((element (Literal IntLiteral)) (shape ())))))))
                (type'
                 ((element (Literal IntLiteral))
                  (shape ((Add ((const 2) (refs ())))))))))))
            ((binding ((name +arg2) (id 29)))
             (value
              (Frame
               ((dimensions (2))
                (elements
                 ((Scalar
                   ((element (Literal (IntLiteral 5)))
                    (type' ((element (Literal IntLiteral)) (shape ())))))
                  (Scalar
                   ((element (Literal (IntLiteral 6)))
                    (type' ((element (Literal IntLiteral)) (shape ())))))))
                (type'
                 ((element (Literal IntLiteral))
                  (shape ((Add ((const 2) (refs ())))))))))))))
          (body
           (PrimitiveCall
            ((op Add)
             (args
              ((Ref
                ((id ((name +arg1) (id 27)))
                 (type' ((element (Literal IntLiteral)) (shape ())))))
               (Ref
                ((id ((name +arg2) (id 29)))
                 (type' ((element (Literal IntLiteral)) (shape ())))))))
             (type' ((element (Literal IntLiteral)) (shape ()))))))
          (type'
           ((element (Literal IntLiteral)) (shape ((Add ((const 2) (refs ())))))))))))
      (type'
       ((element (Literal IntLiteral))
        (shape ((Add ((const 2) (refs ()))) (Add ((const 2) (refs ()))))))))) |}];
  checkAndPrint {| [(frame [0] int) (frame [0] int)] |};
  [%expect
    {|
    (Frame
     ((dimensions (2 0)) (elements ())
      (type'
       ((element (Literal IntLiteral))
        (shape ((Add ((const 2) (refs ()))) (Add ((const 0) (refs ()))))))))) |}];
  checkAndPrint
    {| [[(+ [1 2] [3 4]) (+ [1 2] [3 4]) (+ [1 2] [3 4])] [[4 5] [6 7] [8 9]]] |};
  [%expect
    {|
      (Frame
       ((dimensions (2 3))
        (elements
         ((IntrinsicCall
           (Map (frameShape ((Add ((const 2) (refs ())))))
            (args
             (((binding ((name +arg1) (id 37)))
               (value
                (Frame
                 ((dimensions (2))
                  (elements
                   ((Scalar
                     ((element (Literal (IntLiteral 1)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))
                    (Scalar
                     ((element (Literal (IntLiteral 2)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))))
                  (type'
                   ((element (Literal IntLiteral))
                    (shape ((Add ((const 2) (refs ())))))))))))
              ((binding ((name +arg2) (id 39)))
               (value
                (Frame
                 ((dimensions (2))
                  (elements
                   ((Scalar
                     ((element (Literal (IntLiteral 3)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))
                    (Scalar
                     ((element (Literal (IntLiteral 4)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))))
                  (type'
                   ((element (Literal IntLiteral))
                    (shape ((Add ((const 2) (refs ())))))))))))))
            (body
             (PrimitiveCall
              ((op Add)
               (args
                ((Ref
                  ((id ((name +arg1) (id 37)))
                   (type' ((element (Literal IntLiteral)) (shape ())))))
                 (Ref
                  ((id ((name +arg2) (id 39)))
                   (type' ((element (Literal IntLiteral)) (shape ())))))))
               (type' ((element (Literal IntLiteral)) (shape ()))))))
            (type'
             ((element (Literal IntLiteral)) (shape ((Add ((const 2) (refs ())))))))))
          (IntrinsicCall
           (Map (frameShape ((Add ((const 2) (refs ())))))
            (args
             (((binding ((name +arg1) (id 42)))
               (value
                (Frame
                 ((dimensions (2))
                  (elements
                   ((Scalar
                     ((element (Literal (IntLiteral 1)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))
                    (Scalar
                     ((element (Literal (IntLiteral 2)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))))
                  (type'
                   ((element (Literal IntLiteral))
                    (shape ((Add ((const 2) (refs ())))))))))))
              ((binding ((name +arg2) (id 44)))
               (value
                (Frame
                 ((dimensions (2))
                  (elements
                   ((Scalar
                     ((element (Literal (IntLiteral 3)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))
                    (Scalar
                     ((element (Literal (IntLiteral 4)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))))
                  (type'
                   ((element (Literal IntLiteral))
                    (shape ((Add ((const 2) (refs ())))))))))))))
            (body
             (PrimitiveCall
              ((op Add)
               (args
                ((Ref
                  ((id ((name +arg1) (id 42)))
                   (type' ((element (Literal IntLiteral)) (shape ())))))
                 (Ref
                  ((id ((name +arg2) (id 44)))
                   (type' ((element (Literal IntLiteral)) (shape ())))))))
               (type' ((element (Literal IntLiteral)) (shape ()))))))
            (type'
             ((element (Literal IntLiteral)) (shape ((Add ((const 2) (refs ())))))))))
          (IntrinsicCall
           (Map (frameShape ((Add ((const 2) (refs ())))))
            (args
             (((binding ((name +arg1) (id 47)))
               (value
                (Frame
                 ((dimensions (2))
                  (elements
                   ((Scalar
                     ((element (Literal (IntLiteral 1)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))
                    (Scalar
                     ((element (Literal (IntLiteral 2)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))))
                  (type'
                   ((element (Literal IntLiteral))
                    (shape ((Add ((const 2) (refs ())))))))))))
              ((binding ((name +arg2) (id 49)))
               (value
                (Frame
                 ((dimensions (2))
                  (elements
                   ((Scalar
                     ((element (Literal (IntLiteral 3)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))
                    (Scalar
                     ((element (Literal (IntLiteral 4)))
                      (type' ((element (Literal IntLiteral)) (shape ())))))))
                  (type'
                   ((element (Literal IntLiteral))
                    (shape ((Add ((const 2) (refs ())))))))))))))
            (body
             (PrimitiveCall
              ((op Add)
               (args
                ((Ref
                  ((id ((name +arg1) (id 47)))
                   (type' ((element (Literal IntLiteral)) (shape ())))))
                 (Ref
                  ((id ((name +arg2) (id 49)))
                   (type' ((element (Literal IntLiteral)) (shape ())))))))
               (type' ((element (Literal IntLiteral)) (shape ()))))))
            (type'
             ((element (Literal IntLiteral)) (shape ((Add ((const 2) (refs ())))))))))
          (Frame
           ((dimensions (2))
            (elements
             ((Scalar
               ((element (Literal (IntLiteral 4)))
                (type' ((element (Literal IntLiteral)) (shape ())))))
              (Scalar
               ((element (Literal (IntLiteral 5)))
                (type' ((element (Literal IntLiteral)) (shape ())))))))
            (type'
             ((element (Literal IntLiteral)) (shape ((Add ((const 2) (refs ())))))))))
          (Frame
           ((dimensions (2))
            (elements
             ((Scalar
               ((element (Literal (IntLiteral 6)))
                (type' ((element (Literal IntLiteral)) (shape ())))))
              (Scalar
               ((element (Literal (IntLiteral 7)))
                (type' ((element (Literal IntLiteral)) (shape ())))))))
            (type'
             ((element (Literal IntLiteral)) (shape ((Add ((const 2) (refs ())))))))))
          (Frame
           ((dimensions (2))
            (elements
             ((Scalar
               ((element (Literal (IntLiteral 8)))
                (type' ((element (Literal IntLiteral)) (shape ())))))
              (Scalar
               ((element (Literal (IntLiteral 9)))
                (type' ((element (Literal IntLiteral)) (shape ())))))))
            (type'
             ((element (Literal IntLiteral)) (shape ((Add ((const 2) (refs ())))))))))))
        (type'
         ((element (Literal IntLiteral))
          (shape
           ((Add ((const 2) (refs ()))) (Add ((const 3) (refs ())))
            (Add ((const 2) (refs ()))))))))) |}];
  checkAndPrint {| [[[1 2] [3 4] [5 6]] [[7 8] [9 10] [11 12]]] |};
  [%expect
    {|
    (Frame
     ((dimensions (2 3 2))
      (elements
       ((Scalar
         ((element (Literal (IntLiteral 1)))
          (type' ((element (Literal IntLiteral)) (shape ())))))
        (Scalar
         ((element (Literal (IntLiteral 2)))
          (type' ((element (Literal IntLiteral)) (shape ())))))
        (Scalar
         ((element (Literal (IntLiteral 3)))
          (type' ((element (Literal IntLiteral)) (shape ())))))
        (Scalar
         ((element (Literal (IntLiteral 4)))
          (type' ((element (Literal IntLiteral)) (shape ())))))
        (Scalar
         ((element (Literal (IntLiteral 5)))
          (type' ((element (Literal IntLiteral)) (shape ())))))
        (Scalar
         ((element (Literal (IntLiteral 6)))
          (type' ((element (Literal IntLiteral)) (shape ())))))
        (Scalar
         ((element (Literal (IntLiteral 7)))
          (type' ((element (Literal IntLiteral)) (shape ())))))
        (Scalar
         ((element (Literal (IntLiteral 8)))
          (type' ((element (Literal IntLiteral)) (shape ())))))
        (Scalar
         ((element (Literal (IntLiteral 9)))
          (type' ((element (Literal IntLiteral)) (shape ())))))
        (Scalar
         ((element (Literal (IntLiteral 10)))
          (type' ((element (Literal IntLiteral)) (shape ())))))
        (Scalar
         ((element (Literal (IntLiteral 11)))
          (type' ((element (Literal IntLiteral)) (shape ())))))
        (Scalar
         ((element (Literal (IntLiteral 12)))
          (type' ((element (Literal IntLiteral)) (shape ())))))))
      (type'
       ((element (Literal IntLiteral))
        (shape
         ((Add ((const 2) (refs ()))) (Add ((const 3) (refs ())))
          (Add ((const 2) (refs ()))))))))) |}];
  checkAndPrint "(append{int | 3 2 []} [1 2 3] [4 5])";
  [%expect
    {|
    (Frame
     ((dimensions (5))
      (elements
       ((Scalar
         ((element (Literal (IntLiteral 1)))
          (type' ((element (Literal IntLiteral)) (shape ())))))
        (Scalar
         ((element (Literal (IntLiteral 2)))
          (type' ((element (Literal IntLiteral)) (shape ())))))
        (Scalar
         ((element (Literal (IntLiteral 3)))
          (type' ((element (Literal IntLiteral)) (shape ())))))
        (Scalar
         ((element (Literal (IntLiteral 4)))
          (type' ((element (Literal IntLiteral)) (shape ())))))
        (Scalar
         ((element (Literal (IntLiteral 5)))
          (type' ((element (Literal IntLiteral)) (shape ())))))))
      (type'
       ((element (Literal IntLiteral)) (shape ((Add ((const 5) (refs ()))))))))) |}];
  checkAndPrint "(append{int | 3 2 [1]} [[1] [2] [3]] [[4] [5]])";
  [%expect
    {|
    (Frame
     ((dimensions (5 1))
      (elements
       ((Scalar
         ((element (Literal (IntLiteral 1)))
          (type' ((element (Literal IntLiteral)) (shape ())))))
        (Scalar
         ((element (Literal (IntLiteral 2)))
          (type' ((element (Literal IntLiteral)) (shape ())))))
        (Scalar
         ((element (Literal (IntLiteral 3)))
          (type' ((element (Literal IntLiteral)) (shape ())))))
        (Scalar
         ((element (Literal (IntLiteral 4)))
          (type' ((element (Literal IntLiteral)) (shape ())))))
        (Scalar
         ((element (Literal (IntLiteral 5)))
          (type' ((element (Literal IntLiteral)) (shape ())))))))
      (type'
       ((element (Literal IntLiteral))
        (shape ((Add ((const 5) (refs ()))) (Add ((const 1) (refs ()))))))))) |}];
  checkAndPrint "[[1 1] [2 2] (+ [2 2] 1)]";
  [%expect
    {|
    (Frame
     ((dimensions (3))
      (elements
       ((Frame
         ((dimensions (2))
          (elements
           ((Scalar
             ((element (Literal (IntLiteral 1)))
              (type' ((element (Literal IntLiteral)) (shape ())))))
            (Scalar
             ((element (Literal (IntLiteral 1)))
              (type' ((element (Literal IntLiteral)) (shape ())))))))
          (type'
           ((element (Literal IntLiteral)) (shape ((Add ((const 2) (refs ())))))))))
        (Frame
         ((dimensions (2))
          (elements
           ((Scalar
             ((element (Literal (IntLiteral 2)))
              (type' ((element (Literal IntLiteral)) (shape ())))))
            (Scalar
             ((element (Literal (IntLiteral 2)))
              (type' ((element (Literal IntLiteral)) (shape ())))))))
          (type'
           ((element (Literal IntLiteral)) (shape ((Add ((const 2) (refs ())))))))))
        (IntrinsicCall
         (Map (frameShape ((Add ((const 2) (refs ())))))
          (args
           (((binding ((name +arg1) (id 26)))
             (value
              (Frame
               ((dimensions (2))
                (elements
                 ((Scalar
                   ((element (Literal (IntLiteral 2)))
                    (type' ((element (Literal IntLiteral)) (shape ())))))
                  (Scalar
                   ((element (Literal (IntLiteral 2)))
                    (type' ((element (Literal IntLiteral)) (shape ())))))))
                (type'
                 ((element (Literal IntLiteral))
                  (shape ((Add ((const 2) (refs ())))))))))))))
          (body
           (PrimitiveCall
            ((op Add)
             (args
              ((Ref
                ((id ((name +arg1) (id 26)))
                 (type' ((element (Literal IntLiteral)) (shape ())))))
               (Scalar
                ((element (Literal (IntLiteral 1)))
                 (type' ((element (Literal IntLiteral)) (shape ())))))))
             (type' ((element (Literal IntLiteral)) (shape ()))))))
          (type'
           ((element (Literal IntLiteral)) (shape ((Add ((const 2) (refs ())))))))))))
      (type'
       ((element (Literal IntLiteral))
        (shape ((Add ((const 3) (refs ()))) (Add ((const 2) (refs ()))))))))) |}];
  checkAndPrint "(append{int | 3 2 [2]} [[1 1] [2 2] (+ [2 2] 1)] [[4 4] [5 5]])";
  [%expect
    {|
    (Frame
     ((dimensions (5))
      (elements
       ((Frame
         ((dimensions (2))
          (elements
           ((Scalar
             ((element (Literal (IntLiteral 1)))
              (type' ((element (Literal IntLiteral)) (shape ())))))
            (Scalar
             ((element (Literal (IntLiteral 1)))
              (type' ((element (Literal IntLiteral)) (shape ())))))))
          (type'
           ((element (Literal IntLiteral)) (shape ((Add ((const 2) (refs ())))))))))
        (Frame
         ((dimensions (2))
          (elements
           ((Scalar
             ((element (Literal (IntLiteral 2)))
              (type' ((element (Literal IntLiteral)) (shape ())))))
            (Scalar
             ((element (Literal (IntLiteral 2)))
              (type' ((element (Literal IntLiteral)) (shape ())))))))
          (type'
           ((element (Literal IntLiteral)) (shape ((Add ((const 2) (refs ())))))))))
        (IntrinsicCall
         (Map (frameShape ((Add ((const 2) (refs ())))))
          (args
           (((binding ((name +arg1) (id 30)))
             (value
              (Frame
               ((dimensions (2))
                (elements
                 ((Scalar
                   ((element (Literal (IntLiteral 2)))
                    (type' ((element (Literal IntLiteral)) (shape ())))))
                  (Scalar
                   ((element (Literal (IntLiteral 2)))
                    (type' ((element (Literal IntLiteral)) (shape ())))))))
                (type'
                 ((element (Literal IntLiteral))
                  (shape ((Add ((const 2) (refs ())))))))))))))
          (body
           (PrimitiveCall
            ((op Add)
             (args
              ((Ref
                ((id ((name +arg1) (id 30)))
                 (type' ((element (Literal IntLiteral)) (shape ())))))
               (Scalar
                ((element (Literal (IntLiteral 1)))
                 (type' ((element (Literal IntLiteral)) (shape ())))))))
             (type' ((element (Literal IntLiteral)) (shape ()))))))
          (type'
           ((element (Literal IntLiteral)) (shape ((Add ((const 2) (refs ())))))))))
        (Frame
         ((dimensions (2))
          (elements
           ((Scalar
             ((element (Literal (IntLiteral 4)))
              (type' ((element (Literal IntLiteral)) (shape ())))))
            (Scalar
             ((element (Literal (IntLiteral 4)))
              (type' ((element (Literal IntLiteral)) (shape ())))))))
          (type'
           ((element (Literal IntLiteral)) (shape ((Add ((const 2) (refs ())))))))))
        (Frame
         ((dimensions (2))
          (elements
           ((Scalar
             ((element (Literal (IntLiteral 5)))
              (type' ((element (Literal IntLiteral)) (shape ())))))
            (Scalar
             ((element (Literal (IntLiteral 5)))
              (type' ((element (Literal IntLiteral)) (shape ())))))))
          (type'
           ((element (Literal IntLiteral)) (shape ((Add ((const 2) (refs ())))))))))))
      (type'
       ((element (Literal IntLiteral))
        (shape ((Add ((const 5) (refs ()))) (Add ((const 2) (refs ()))))))))) |}]
;;
