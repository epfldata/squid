// Automatically-generated code

// === Init ===

// Transfo time: 0ms  Stringifying time: 10ms

((xs_0: scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]]) => {
  val x_1 = xs_0.size;
  val x_2 = new sfusion.Sequence[scala.collection.IndexedSeq[scala.Int]]((() => sfusion.impl.`package`.fromIndexed[scala.collection.IndexedSeq[scala.Int]](xs_0)), scala.`package`.Left.apply[scala.Int, scala.Nothing](x_1));
  val x_5 = x_2.map[sfusion.Sequence[scala.Int]](((is_3: scala.collection.IndexedSeq[scala.Int]) => {
    val x_4 = is_3.size;
    new sfusion.Sequence[scala.Int]((() => sfusion.impl.`package`.fromIndexed[scala.Int](is_3)), scala.`package`.Left.apply[scala.Int, scala.Nothing](x_4))
  }));
  val x_7 = x_5.flatMap[scala.Int](((b_6: sfusion.Sequence[scala.Int]) => b_6));
  x_7.fold[scala.Int](123)(((x$5_8: scala.Int, x$6_9: scala.Int) => x$5_8.+(x$6_9)))
})

// === HL ===

// Transfo time: 5ms  Stringifying time: 12ms

((xs_0: scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]]) => {
  val x_1 = xs_0.size;
  val x_2 = new sfusion.Sequence[scala.collection.IndexedSeq[scala.Int]]((() => sfusion.impl.`package`.fromIndexed[scala.collection.IndexedSeq[scala.Int]](xs_0)), scala.`package`.Left.apply[scala.Int, scala.Nothing](x_1));
  val x_5 = x_2.flatMap[scala.Int](((x_3: scala.collection.IndexedSeq[scala.Int]) => {
    val x_4 = x_3.size;
    new sfusion.Sequence[scala.Int]((() => sfusion.impl.`package`.fromIndexed[scala.Int](x_3)), scala.`package`.Left.apply[scala.Int, scala.Nothing](x_4))
  }));
  x_5.fold[scala.Int](123)(((x$5_6: scala.Int, x$6_7: scala.Int) => x$5_6.+(x$6_7)))
})

// === Impl ===

// Transfo time: 6ms  Stringifying time: 18ms

((xs_0: scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]]) => {
  val x_1 = xs_0.size;
  val x_2 = new sfusion.Sequence[scala.collection.IndexedSeq[scala.Int]]((() => sfusion.impl.`package`.fromIndexed[scala.collection.IndexedSeq[scala.Int]](xs_0)), scala.`package`.Left.apply[scala.Int, scala.Nothing](x_1));
  val x_9 = new sfusion.Sequence[scala.Int]((() => {
    val x_3 = x_2.under;
    val x_4 = x_3.apply();
    sfusion.impl.`package`.flatMap[scala.collection.IndexedSeq[scala.Int], scala.Int](x_4)(((x_5: scala.collection.IndexedSeq[scala.Int]) => {
      val x_6 = x_5.size;
      val x_7 = new sfusion.Sequence[scala.Int]((() => sfusion.impl.`package`.fromIndexed[scala.Int](x_5)), scala.`package`.Left.apply[scala.Int, scala.Nothing](x_6));
      val x_8 = x_7.under;
      x_8.apply()
    }))
  }), scala.`package`.Right.apply[scala.Nothing, scala.Boolean](true));
  val x_10 = x_9.under;
  val x_11 = x_10.apply();
  sfusion.impl.`package`.fold[scala.Int, scala.Int](x_11)(123)(((x$5_12: scala.Int, x$6_13: scala.Int) => x$5_12.+(x$6_13)))
})

// === CtorInline ===

// Transfo time: 4ms  Stringifying time: 6ms

((xs_0: scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]]) => {
  val x_1 = xs_0.size;
  val x_2 = sfusion.impl.`package`.fromIndexed[scala.collection.IndexedSeq[scala.Int]](xs_0);
  val x_5 = sfusion.impl.`package`.flatMap[scala.collection.IndexedSeq[scala.Int], scala.Int](x_2)(((x_3: scala.collection.IndexedSeq[scala.Int]) => {
    val x_4 = x_3.size;
    sfusion.impl.`package`.fromIndexed[scala.Int](x_3)
  }));
  sfusion.impl.`package`.fold[scala.Int, scala.Int](x_5)(123)(((x$5_6: scala.Int, x$6_7: scala.Int) => x$5_6.+(x$6_7)))
})

// === ImplOptim ===

// Transfo time: 0ms  Stringifying time: 2ms

// Same as above.

// === Imperative ===

// Transfo time: 7ms  Stringifying time: 20ms

((xs_0: scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]]) => {
  val x_1 = xs_0.size;
  val x_2 = xs_0.length;
  var i_3: scala.Int = 0;
  val x_20 = sfusion.impl.`package`.flatMap[scala.collection.IndexedSeq[scala.Int], scala.Int](((k_4: scala.Function1[scala.collection.IndexedSeq[scala.Int], scala.Boolean]) => {
    while ({
      val x_5 = i_3;
      x_5.<(x_2).&&({
        val x_6 = i_3;
        val x_7 = xs_0.apply(x_6);
        val x_8 = i_3;
        i_3 = x_8.+(1);
        k_4(x_7)
      })
    }) 
      ()
    ;
    val x_9 = i_3;
    x_9.==(x_2)
  }))(((x_10: scala.collection.IndexedSeq[scala.Int]) => {
    val x_11 = x_10.size;
    val x_12 = x_10.length;
    var i_13: scala.Int = 0;
    ((k_14: scala.Function1[scala.Int, scala.Boolean]) => {
      while ({
        val x_15 = i_13;
        x_15.<(x_12).&&({
          val x_16 = i_13;
          val x_17 = x_10.apply(x_16);
          val x_18 = i_13;
          i_13 = x_18.+(1);
          k_14(x_17)
        })
      }) 
        ()
      ;
      val x_19 = i_13;
      x_19.==(x_12)
    })
  }));
  var cur_21: scala.Int = 123;
  x_20(((a_22: scala.Int) => {
    val x_23 = cur_21;
    cur_21 = x_23.+(a_22);
    true
  }));
  cur_21
})

// === FlatMapFusion ===

// Transfo time: 26ms  Stringifying time: 43ms

((xs_0: scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]]) => {
  val x_1 = xs_0.size;
  val x_2 = xs_0.length;
  var i_3: scala.Int = 0;
  var aVar_4: scala.Option[scala.collection.IndexedSeq[scala.Int]] = scala.None;
  var envVar_5: scala.Option[scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.Var[scala.Int]]]] = scala.None;
  var cur_6: scala.Int = 123;
  var completed_7: scala.Boolean = false;
  var continue_8: scala.Boolean = false;
  while ({
    val x_9 = envVar_5;
    if (x_9.isDefined.`unary_!`)
      {
        while ({
          val x_10 = i_3;
          x_10.<(x_2).&&({
            val x_11 = i_3;
            val x_12 = xs_0.apply(x_11);
            val x_13 = i_3;
            i_3 = x_13.+(1);
            aVar_4 = scala.Some.apply[scala.collection.IndexedSeq[scala.Int]](x_12);
            val ClosureVar_14 = x_12.size;
            val ClosureVar_15 = x_12.length;
            var v_16: scala.Int = 0;
            envVar_5 = scala.Some.apply[scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.Var[scala.Int]]]](scala.Tuple2.apply[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.Var[scala.Int]]](ClosureVar_14, scala.Tuple2.apply[scala.Int, squid.lib.`package`.Var[scala.Int]](ClosureVar_15, new squid.lib.MutVarProxy[scala.Int](v_16, ((a) => v_16 = a)))));
            false
          })
        }) 
          ()
        ;
        val x_17 = i_3;
        x_17.==(x_2)
      }
    else
      ();
    val x_18 = envVar_5;
    if (x_18.isDefined.`unary_!`)
      completed_7 = true
    else
      {
        val x_19 = envVar_5;
        while ({
          val x_20 = x_19.get._2._2.!;
          x_20.<(x_19.get._2._1).&&({
            val sch_21 = x_19.get;
            val sch_22 = sch_21._2;
            val sch_23 = sch_22._2;
            val x_24 = sch_23.!;
            val x_25 = aVar_4;
            val x_26 = x_25.get.apply(x_24);
            val x_27 = sch_23.!;
            sch_23.:=(x_27.+(1));
            val x_28 = cur_6;
            cur_6 = x_28.+(x_26);
            continue_8 = true;
            continue_8
          })
        }) 
          ()
        ;
        val sch_29 = x_19.get;
        val sch_30 = sch_29._2;
        val x_31 = sch_30._2.!;
        if (x_31.==(sch_30._1))
          envVar_5 = scala.None
        else
          ()
      };
    val x_32 = completed_7;
    x_32.`unary_!`.&&(continue_8)
  }) 
    ()
  ;
  completed_7;
  cur_6
})

// === LateImperative ===

// Transfo time: 0ms  Stringifying time: 31ms

// Same as above.

// === VarFlattening ===

// Transfo time: 53ms  Stringifying time: 36ms

((xs_0: scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]]) => {
  val sch_1 = squid.lib.`package`.uncheckedNullValue[scala.Int];
  val x_2 = xs_0.size;
  val x_3 = xs_0.length;
  var i_4: scala.Int = 0;
  var isDefined_5: scala.Boolean = false;
  var optVal_6: scala.collection.IndexedSeq[scala.Int] = squid.lib.`package`.uncheckedNullValue[scala.collection.IndexedSeq[scala.Int]];
  var isDefined_7: scala.Boolean = false;
  var lhs_8: scala.Int = sch_1;
  var lhs_9: scala.Int = sch_1;
  var flatVar_10: scala.Int = sch_1;
  var cur_11: scala.Int = 123;
  var completed_12: scala.Boolean = false;
  var continue_13: scala.Boolean = false;
  while ({
    val x_14 = isDefined_7;
    if (x_14.`unary_!`)
      {
        while ({
          val x_15 = i_4;
          x_15.<(x_3).&&({
            val x_16 = i_4;
            val x_17 = xs_0.apply(x_16);
            val x_18 = i_4;
            i_4 = x_18.+(1);
            optVal_6 = x_17;
            isDefined_5 = true;
            val ClosureVar_19 = x_17.size;
            val ClosureVar_20 = x_17.length;
            var v_21: scala.Int = 0;
            lhs_8 = ClosureVar_19;
            lhs_9 = ClosureVar_20;
            val x_22 = v_21;
            flatVar_10 = x_22;
            isDefined_7 = true;
            false
          })
        }) 
          ()
        ;
        val x_23 = i_4;
        x_23.==(x_3)
      }
    else
      ();
    val x_24 = isDefined_7;
    if (x_24.`unary_!`)
      completed_12 = true
    else
      {
        while ({
          val x_25 = flatVar_10;
          val x_26 = lhs_9;
          x_25.<(x_26).&&({
            val x_27 = flatVar_10;
            val x_28 = optVal_6;
            val x_29 = x_28.apply(x_27);
            val x_30 = flatVar_10;
            flatVar_10 = x_30.+(1);
            val x_31 = cur_11;
            cur_11 = x_31.+(x_29);
            continue_13 = true;
            continue_13
          })
        }) 
          ()
        ;
        val x_32 = flatVar_10;
        val x_33 = lhs_9;
        if (x_32.==(x_33))
          isDefined_7 = false
        else
          ()
      };
    val x_34 = completed_12;
    x_34.`unary_!`.&&(continue_13)
  }) 
    ()
  ;
  completed_12;
  cur_11
})

// === Low-Level Norm ===

// Transfo time: 18ms  Stringifying time: 42ms

((xs_0: scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]]) => {
  val x_1 = xs_0.size;
  val x_2 = xs_0.length;
  var i_3: scala.Int = 0;
  var isDefined_4: scala.Boolean = false;
  var optVal_5: scala.collection.IndexedSeq[scala.Int] = null;
  var isDefined_6: scala.Boolean = false;
  var lhs_7: scala.Int = 0;
  var lhs_8: scala.Int = 0;
  var flatVar_9: scala.Int = 0;
  var cur_10: scala.Int = 123;
  var completed_11: scala.Boolean = false;
  var continue_12: scala.Boolean = false;
  while ({
    val x_13 = isDefined_6;
    if (x_13)
      ()
    else
      {
        val x_14 = i_3;
        if (x_14.<(x_2))
          {
            val x_15 = i_3;
            val x_16 = xs_0.apply(x_15);
            val x_17 = i_3;
            i_3 = x_17.+(1);
            optVal_5 = x_16;
            isDefined_4 = true;
            val ClosureVar_18 = x_16.size;
            val ClosureVar_19 = x_16.length;
            var v_20: scala.Int = 0;
            lhs_7 = ClosureVar_18;
            lhs_8 = ClosureVar_19;
            val x_21 = v_20;
            flatVar_9 = x_21;
            isDefined_6 = true
          }
        else
          ();
        val x_22 = i_3;
        x_22.==(x_2)
      };
    val x_23 = isDefined_6;
    if (x_23)
      {
        while ({
          val x_24 = flatVar_9;
          val x_25 = lhs_8;
          x_24.<(x_25).&&({
            val x_26 = flatVar_9;
            val x_27 = optVal_5;
            val x_28 = x_27.apply(x_26);
            val x_29 = flatVar_9;
            flatVar_9 = x_29.+(1);
            val x_30 = cur_10;
            cur_10 = x_30.+(x_28);
            continue_12 = true;
            continue_12
          })
        }) 
          ()
        ;
        val x_31 = flatVar_9;
        val x_32 = lhs_8;
        if (x_31.==(x_32))
          isDefined_6 = false
        else
          ()
      }
    else
      completed_11 = true;
    val x_33 = completed_11;
    x_33.`unary_!`.&&(continue_12)
  }) 
    ()
  ;
  completed_11;
  cur_10
})

// === ReNorm (should be the same) ===

// Transfo time: 9ms  Stringifying time: 50ms

// Same as above.
