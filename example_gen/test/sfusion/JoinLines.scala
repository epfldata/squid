// Automatically-generated code

// === Init ===

// Transfo time: 0ms  Stringifying time: 12ms

((x$1_0: scala.collection.Iterable[java.lang.String]) => {
  val x_1 = sfusion.algo.`package`.joinLinesSimple$default$2;
  val x_2 = x$1_0.isEmpty;
  if (x_2)
    ""
  else
    {
      val x_3 = x$1_0.tail;
      val x_5 = new sfusion.Sequence[java.lang.String]((() => {
        val x_4 = x_3.iterator;
        sfusion.impl.`package`.fromIterator[java.lang.String](x_4)
      }), scala.`package`.Right.apply[scala.Nothing, scala.Boolean](false));
      val x_6 = x$1_0.head;
      x_5.fold[java.lang.String](x_6)(((x$8_7: java.lang.String, x$9_8: java.lang.String) => x$8_7.+(x_1).+(x$9_8)))
    }
})

// === HL ===

// Transfo time: 0ms  Stringifying time: 8ms

// Same as above.

// === Impl ===

// Transfo time: 2ms  Stringifying time: 17ms

((x$1_0: scala.collection.Iterable[java.lang.String]) => {
  val x_1 = sfusion.algo.`package`.joinLinesSimple$default$2;
  val x_2 = x$1_0.isEmpty;
  if (x_2)
    ""
  else
    {
      val x_3 = x$1_0.tail;
      val x_5 = new sfusion.Sequence[java.lang.String]((() => {
        val x_4 = x_3.iterator;
        sfusion.impl.`package`.fromIterator[java.lang.String](x_4)
      }), scala.`package`.Right.apply[scala.Nothing, scala.Boolean](false));
      val x_6 = x$1_0.head;
      val x_7 = x_5.under;
      val x_8 = x_7.apply();
      sfusion.impl.`package`.fold[java.lang.String, java.lang.String](x_8)(x_6)(((x$8_9: java.lang.String, x$9_10: java.lang.String) => x$8_9.+(x_1).+(x$9_10)))
    }
})

// === CtorInline ===

// Transfo time: 3ms  Stringifying time: 12ms

((x$1_0: scala.collection.Iterable[java.lang.String]) => {
  val x_1 = sfusion.algo.`package`.joinLinesSimple$default$2;
  val x_2 = x$1_0.isEmpty;
  if (x_2)
    ""
  else
    {
      val x_3 = x$1_0.tail;
      val x_4 = x$1_0.head;
      val x_5 = x_3.iterator;
      val x_6 = sfusion.impl.`package`.fromIterator[java.lang.String](x_5);
      sfusion.impl.`package`.fold[java.lang.String, java.lang.String](x_6)(x_4)(((x$8_7: java.lang.String, x$9_8: java.lang.String) => x$8_7.+(x_1).+(x$9_8)))
    }
})

// === ImplOptim ===

// Transfo time: 11ms  Stringifying time: 15ms

((x$1_0: scala.collection.Iterable[java.lang.String]) => {
  val x_1 = sfusion.algo.`package`.joinLinesSimple$default$2;
  val x_2 = x$1_0.isEmpty;
  if (x_2)
    ""
  else
    {
      val x_3 = x$1_0.tail;
      val x_4 = x$1_0.head;
      val x_5 = x_3.iterator;
      val x_6 = sfusion.impl.`package`.fromIterator[java.lang.String](x_5);
      val strAcc_7 = new scala.collection.mutable.StringBuilder();
      strAcc_7.++=(x_4);
      sfusion.impl.`package`.foreach[java.lang.String](x_6)(((s_8: java.lang.String) => {
        strAcc_7.++=(x_1.toString().+(s_8).toString());
        ()
      }));
      strAcc_7.result()
    }
})

// === Imperative ===

// Transfo time: 9ms  Stringifying time: 19ms

((x$1_0: scala.collection.Iterable[java.lang.String]) => {
  val x_1 = sfusion.algo.`package`.joinLinesSimple$default$2;
  val x_2 = x$1_0.isEmpty;
  if (x_2)
    ""
  else
    {
      val x_3 = x$1_0.tail;
      val x_4 = x$1_0.head;
      val x_5 = x_3.iterator;
      val strAcc_6 = new scala.collection.mutable.StringBuilder();
      strAcc_6.++=(x_4);
      while ({
        val x_7 = x_5.hasNext;
        x_7.&&({
          val x_8 = x_5.next();
          strAcc_6.++=(x_1.toString().+(x_8).toString());
          true
        })
      }) 
        ()
      ;
      val x_9 = x_5.hasNext;
      strAcc_6.result()
    }
})

// === FlatMapFusion ===

// Transfo time: 0ms  Stringifying time: 14ms

// Same as above.

// === LateImperative ===

// Transfo time: 0ms  Stringifying time: 13ms

// Same as above.

// === VarFlattening ===

// Transfo time: 0ms  Stringifying time: 12ms

// Same as above.

// === Low-Level Norm ===

// Transfo time: 7ms  Stringifying time: 13ms

((x$1_0: scala.collection.Iterable[java.lang.String]) => {
  val x_1 = sfusion.algo.`package`.joinLinesSimple$default$2;
  val x_2 = x$1_0.isEmpty;
  if (x_2)
    ""
  else
    {
      val x_3 = x$1_0.tail;
      val x_4 = x$1_0.head;
      val x_5 = x_3.iterator;
      val strAcc_6 = new scala.collection.mutable.StringBuilder();
      strAcc_6.++=(x_4);
      while ({
        val x_7 = x_5.hasNext;
        if (x_7)
          {
            val x_8 = x_5.next();
            strAcc_6.++=(x_1.toString().+(x_8).toString());
            ()
          }
        else
          ();
        x_7
      }) 
        ()
      ;
      val x_9 = x_5.hasNext;
      strAcc_6.result()
    }
})

// === ReNorm (should be the same) ===

// Transfo time: 3ms  Stringifying time: 5ms

// Same as above.
