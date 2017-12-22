// Automatically-generated code

// === Init ===

// Transfo time: 0ms  Stringifying time: 67ms

{
  val x_0 = scala.Predef.intWrapper(1);
  val x_1 = x_0.to(10);
  val x_2 = ((x_1): scala.collection.IndexedSeq[scala.Int]).size;
  val x_3 = new sfusion.Sequence[scala.Int]((() => sfusion.impl.`package`.fromIndexed[scala.Int](((x_1): scala.collection.IndexedSeq[scala.Int]))), scala.`package`.Left.apply[scala.Int, scala.Nothing](x_2));
  x_3.show(10)
}

// === HL ===

// Transfo time: 1ms  Stringifying time: 12ms

// Same as above.

// === Impl ===

// Transfo time: 31ms  Stringifying time: 50ms

{
  val x_0 = scala.Predef.intWrapper(1);
  val x_1 = x_0.to(10);
  val x_2 = ((x_1): scala.collection.IndexedSeq[scala.Int]).size;
  val x_3 = new sfusion.Sequence[scala.Int]((() => sfusion.impl.`package`.fromIndexed[scala.Int](((x_1): scala.collection.IndexedSeq[scala.Int]))), scala.`package`.Left.apply[scala.Int, scala.Nothing](x_2));
  val x_4 = scala.StringContext.apply("Sequence(", ")");
  var truncated_5: scala.Boolean = true;
  val x_6 = x_3.under;
  val x_7 = x_6.apply();
  val x_8 = sfusion.impl.`package`.onFinish[scala.Int](x_7)((() => truncated_5 = false));
  val withSep_14 = sfusion.impl.`package`.mapHeadTail[scala.Int, java.lang.String](x_8)(((a_9: scala.Int) => {
    val sch_10 = "";
    val x_11 = scala.StringContext.apply(sch_10, sch_10);
    x_11.s(a_9)
  }))(((a_12: scala.Int) => {
    val x_13 = scala.StringContext.apply(",", "");
    x_13.s(a_12)
  }));
  val withTrunc_15 = sfusion.impl.`package`.take[java.lang.String](withSep_14)(10);
  val flat_18 = sfusion.impl.`package`.fold[java.lang.String, java.lang.String](withTrunc_15)("")(((x$4_16: java.lang.String, x$5_17: java.lang.String) => x$4_16.+(x$5_17)));
  val x_19 = truncated_5;
  x_4.s(if (x_19)
    flat_18.+(",...")
  else
    flat_18)
}

// === CtorInline ===

// Transfo time: 24ms  Stringifying time: 29ms

{
  val x_0 = scala.Predef.intWrapper(1);
  val x_1 = x_0.to(10);
  val sch_2 = ((x_1): scala.collection.IndexedSeq[scala.Int]);
  val x_3 = sch_2.size;
  val x_4 = scala.StringContext.apply("Sequence(", ")");
  var truncated_5: scala.Boolean = true;
  val x_6 = sfusion.impl.`package`.fromIndexed[scala.Int](sch_2);
  val x_7 = sfusion.impl.`package`.onFinish[scala.Int](x_6)((() => truncated_5 = false));
  val withSep_13 = sfusion.impl.`package`.mapHeadTail[scala.Int, java.lang.String](x_7)(((a_8: scala.Int) => {
    val sch_9 = "";
    val x_10 = scala.StringContext.apply(sch_9, sch_9);
    x_10.s(a_8)
  }))(((a_11: scala.Int) => {
    val x_12 = scala.StringContext.apply(",", "");
    x_12.s(a_11)
  }));
  val withTrunc_14 = sfusion.impl.`package`.take[java.lang.String](withSep_13)(10);
  val flat_17 = sfusion.impl.`package`.fold[java.lang.String, java.lang.String](withTrunc_14)("")(((x$4_15: java.lang.String, x$5_16: java.lang.String) => x$4_15.+(x$5_16)));
  val x_18 = truncated_5;
  x_4.s(if (x_18)
    flat_17.+(",...")
  else
    flat_17)
}

// === ImplOptim ===

// Transfo time: 21ms  Stringifying time: 35ms

{
  val x_0 = scala.Predef.intWrapper(1);
  val x_1 = x_0.to(10);
  val sch_2 = ((x_1): scala.collection.IndexedSeq[scala.Int]);
  val x_3 = sch_2.size;
  val x_4 = scala.StringContext.apply("Sequence(", ")");
  var truncated_5: scala.Boolean = true;
  val x_6 = sfusion.impl.`package`.fromIndexed[scala.Int](sch_2);
  val x_7 = sfusion.impl.`package`.onFinish[scala.Int](x_6)((() => truncated_5 = false));
  val withSep_13 = sfusion.impl.`package`.mapHeadTail[scala.Int, java.lang.String](x_7)(((a_8: scala.Int) => {
    val sch_9 = "";
    val x_10 = scala.StringContext.apply(sch_9, sch_9);
    x_10.s(a_8)
  }))(((a_11: scala.Int) => {
    val x_12 = scala.StringContext.apply(",", "");
    x_12.s(a_11)
  }));
  val withTrunc_14 = sfusion.impl.`package`.take[java.lang.String](withSep_13)(10);
  val strAcc_15 = new scala.collection.mutable.StringBuilder();
  sfusion.impl.`package`.foreach[java.lang.String](withTrunc_14)(((s_16: java.lang.String) => {
    strAcc_15.++=(s_16.toString());
    ()
  }));
  val x_17 = strAcc_15.result();
  val x_18 = truncated_5;
  x_4.s(if (x_18)
    x_17.+(",...")
  else
    x_17)
}

// === Imperative ===

// Transfo time: 67ms  Stringifying time: 48ms

{
  val x_0 = scala.Predef.intWrapper(1);
  val x_1 = x_0.to(10);
  val x_2 = ((x_1): scala.collection.IndexedSeq[scala.Int]).size;
  val x_3 = scala.StringContext.apply("Sequence(", ")");
  var truncated_4: scala.Boolean = true;
  val x_5 = ((x_1): scala.collection.IndexedSeq[scala.Int]).length;
  var i_6: scala.Int = 0;
  var first_7: scala.Boolean = true;
  var taken_8: scala.Int = 0;
  val strAcc_9 = new scala.collection.mutable.StringBuilder();
  while ({
    val x_10 = i_6;
    x_10.<(x_5).&&({
      val x_11 = i_6;
      val x_12 = ((x_1): scala.collection.IndexedSeq[scala.Int]).apply(x_11);
      val x_13 = i_6;
      i_6 = x_13.+(1);
      val x_14 = first_7;
      val x_18 = if (x_14)
        {
          val sch_15 = "";
          first_7 = false;
          val x_16 = scala.StringContext.apply(sch_15, sch_15);
          x_16.s(x_12)
        }
      else
        {
          val x_17 = scala.StringContext.apply(",", "");
          x_17.s(x_12)
        };
      val x_19 = taken_8;
      x_19.<(10).&&({
        val x_20 = taken_8;
        taken_8 = x_20.+(1);
        strAcc_9.++=(x_18.toString());
        true.&&({
          val x_21 = taken_8;
          x_21.<(10)
        })
      })
    })
  }) 
    ()
  ;
  val x_22 = i_6;
  val sch_23 = x_22.==(x_5);
  if (sch_23)
    truncated_4 = false
  else
    ();
  sch_23.||({
    val x_24 = taken_8;
    x_24.==(10)
  });
  val x_25 = strAcc_9.result();
  val x_26 = truncated_4;
  x_3.s(if (x_26)
    x_25.+(",...")
  else
    x_25)
}

// === FlatMapFusion ===

// Transfo time: 0ms  Stringifying time: 32ms

// Same as above.

// === LateImperative ===

// Transfo time: 0ms  Stringifying time: 34ms

// Same as above.

// === VarFlattening ===

// Transfo time: 3ms  Stringifying time: 25ms

// Same as above.

// === Low-Level Norm ===

// Transfo time: 56ms  Stringifying time: 76ms

{
  val x_0 = scala.Predef.intWrapper(1);
  val x_1 = x_0.to(10);
  val x_2 = ((x_1): scala.collection.IndexedSeq[scala.Int]).size;
  val x_3 = scala.StringContext.apply("Sequence(", ")");
  var truncated_4: scala.Boolean = true;
  val x_5 = ((x_1): scala.collection.IndexedSeq[scala.Int]).length;
  var i_6: scala.Int = 0;
  var first_7: scala.Boolean = true;
  var taken_8: scala.Int = 0;
  val strAcc_9 = new scala.collection.mutable.StringBuilder();
  while ({
    val x_10 = i_6;
    x_10.<(x_5).&&({
      val x_11 = i_6;
      val x_12 = ((x_1): scala.collection.IndexedSeq[scala.Int]).apply(x_11);
      val x_13 = i_6;
      i_6 = x_13.+(1);
      val x_14 = first_7;
      val x_18 = if (x_14)
        {
          val sch_15 = "";
          first_7 = false;
          val x_16 = scala.StringContext.apply(sch_15, sch_15);
          x_16.s(x_12)
        }
      else
        {
          val x_17 = scala.StringContext.apply(",", "");
          x_17.s(x_12)
        };
      val x_19 = taken_8;
      x_19.<(10).&&({
        val x_20 = taken_8;
        taken_8 = x_20.+(1);
        strAcc_9.++=(x_18.toString());
        val x_21 = taken_8;
        x_21.<(10)
      })
    })
  }) 
    ()
  ;
  val x_22 = i_6;
  val sch_23 = x_22.==(x_5);
  if (sch_23)
    truncated_4 = false
  else
    ();
  val x_25 = sch_23.`unary_!`.&&({
    val x_24 = taken_8;
    x_24.==(10).`unary_!`
  });
  val x_26 = strAcc_9.result();
  val x_27 = truncated_4;
  x_3.s(if (x_27)
    x_26.+(",...")
  else
    x_26)
}

// === ReNorm (should be the same) ===

// Transfo time: 32ms  Stringifying time: 42ms

// Same as above.
