// Automatically-generated code

// === Init ===

// Transfo time: 0ms  Stringifying time: 23ms

((xs_0: scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]]]) => {
  val sch_1 = scala.`package`.Left;
  val x_2 = xs_0.size;
  val x_3 = new sfusion.Sequence[scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]]]((() => sfusion.impl.`package`.fromIndexed[scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]]](xs_0)), sch_1.apply[scala.Int, scala.Nothing](x_2));
  val x_9 = x_3.flatMap[scala.Int](((a_4: scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]]) => {
    val x_5 = a_4.size;
    val x_6 = new sfusion.Sequence[scala.collection.IndexedSeq[scala.Int]]((() => sfusion.impl.`package`.fromIndexed[scala.collection.IndexedSeq[scala.Int]](a_4)), sch_1.apply[scala.Int, scala.Nothing](x_5));
    x_6.flatMap[scala.Int](((b_7: scala.collection.IndexedSeq[scala.Int]) => {
      val x_8 = b_7.size;
      new sfusion.Sequence[scala.Int]((() => sfusion.impl.`package`.fromIndexed[scala.Int](b_7)), sch_1.apply[scala.Int, scala.Nothing](x_8))
    }))
  }));
  x_9.fold[scala.Int](123)(((x$3_10: scala.Int, x$4_11: scala.Int) => x$3_10.+(x$4_11)))
})

// === HL ===

// Transfo time: 0ms  Stringifying time: 8ms

// Same as above.

// === Impl ===

// Transfo time: 4ms  Stringifying time: 48ms

((xs_0: scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]]]) => {
  val sch_1 = scala.`package`.Left;
  val sch_2 = scala.`package`.Right.apply[scala.Nothing, scala.Boolean](true);
  val x_3 = xs_0.size;
  val x_4 = new sfusion.Sequence[scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]]]((() => sfusion.impl.`package`.fromIndexed[scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]]](xs_0)), sch_1.apply[scala.Int, scala.Nothing](x_3));
  val x_18 = new sfusion.Sequence[scala.Int]((() => {
    val x_5 = x_4.under;
    val x_6 = x_5.apply();
    sfusion.impl.`package`.flatMap[scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]], scala.Int](x_6)(((x_7: scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]]) => {
      val x_8 = x_7.size;
      val x_9 = new sfusion.Sequence[scala.collection.IndexedSeq[scala.Int]]((() => sfusion.impl.`package`.fromIndexed[scala.collection.IndexedSeq[scala.Int]](x_7)), sch_1.apply[scala.Int, scala.Nothing](x_8));
      val x_16 = new sfusion.Sequence[scala.Int]((() => {
        val x_10 = x_9.under;
        val x_11 = x_10.apply();
        sfusion.impl.`package`.flatMap[scala.collection.IndexedSeq[scala.Int], scala.Int](x_11)(((x_12: scala.collection.IndexedSeq[scala.Int]) => {
          val x_13 = x_12.size;
          val x_14 = new sfusion.Sequence[scala.Int]((() => sfusion.impl.`package`.fromIndexed[scala.Int](x_12)), sch_1.apply[scala.Int, scala.Nothing](x_13));
          val x_15 = x_14.under;
          x_15.apply()
        }))
      }), sch_2);
      val x_17 = x_16.under;
      x_17.apply()
    }))
  }), sch_2);
  val x_19 = x_18.under;
  val x_20 = x_19.apply();
  sfusion.impl.`package`.fold[scala.Int, scala.Int](x_20)(123)(((x$3_21: scala.Int, x$4_22: scala.Int) => x$3_21.+(x$4_22)))
})

// === CtorInline ===

// Transfo time: 7ms  Stringifying time: 18ms

((xs_0: scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]]]) => {
  val x_1 = xs_0.size;
  val x_2 = sfusion.impl.`package`.fromIndexed[scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]]](xs_0);
  val x_8 = sfusion.impl.`package`.flatMap[scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]], scala.Int](x_2)(((x_3: scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]]) => {
    val x_4 = x_3.size;
    val x_5 = sfusion.impl.`package`.fromIndexed[scala.collection.IndexedSeq[scala.Int]](x_3);
    sfusion.impl.`package`.flatMap[scala.collection.IndexedSeq[scala.Int], scala.Int](x_5)(((x_6: scala.collection.IndexedSeq[scala.Int]) => {
      val x_7 = x_6.size;
      sfusion.impl.`package`.fromIndexed[scala.Int](x_6)
    }))
  }));
  sfusion.impl.`package`.fold[scala.Int, scala.Int](x_8)(123)(((x$3_9: scala.Int, x$4_10: scala.Int) => x$3_9.+(x$4_10)))
})

// === ImplOptim ===

// Transfo time: 0ms  Stringifying time: 6ms

// Same as above.

// === Imperative ===

// Transfo time: 11ms  Stringifying time: 52ms

((xs_0: scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]]]) => {
  val x_1 = xs_0.size;
  val x_2 = xs_0.length;
  var i_3: scala.Int = 0;
  val x_30 = sfusion.impl.`package`.flatMap[scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]], scala.Int](((k_4: scala.Function1[scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]], scala.Boolean]) => {
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
  }))(((x_10: scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]]) => {
    val x_11 = x_10.size;
    val x_12 = x_10.length;
    var i_13: scala.Int = 0;
    sfusion.impl.`package`.flatMap[scala.collection.IndexedSeq[scala.Int], scala.Int](((k_14: scala.Function1[scala.collection.IndexedSeq[scala.Int], scala.Boolean]) => {
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
    }))(((x_20: scala.collection.IndexedSeq[scala.Int]) => {
      val x_21 = x_20.size;
      val x_22 = x_20.length;
      var i_23: scala.Int = 0;
      ((k_24: scala.Function1[scala.Int, scala.Boolean]) => {
        while ({
          val x_25 = i_23;
          x_25.<(x_22).&&({
            val x_26 = i_23;
            val x_27 = x_20.apply(x_26);
            val x_28 = i_23;
            i_23 = x_28.+(1);
            k_24(x_27)
          })
        }) 
          ()
        ;
        val x_29 = i_23;
        x_29.==(x_22)
      })
    }))
  }));
  var cur_31: scala.Int = 123;
  x_30(((a_32: scala.Int) => {
    val x_33 = cur_31;
    cur_31 = x_33.+(a_32);
    true
  }));
  cur_31
})

// === FlatMapFusion ===

// Transfo time: 58ms  Stringifying time: 133ms

((xs_0: scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]]]) => {
  val x_1 = xs_0.size;
  val x_2 = xs_0.length;
  var i_3: scala.Int = 0;
  var aVar_4: scala.Option[scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]]] = scala.None;
  var envVar_5: scala.Option[scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.MutVar[scala.Int], scala.Tuple2[squid.lib.`package`.MutVar[scala.Option[scala.collection.IndexedSeq[scala.Int]]], squid.lib.`package`.MutVar[scala.Option[scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.MutVar[scala.Int]]]]]]]]]] = scala.None;
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
            aVar_4 = scala.Some.apply[scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]]](x_12);
            val ClosureVar_14 = x_12.size;
            val ClosureVar_15 = x_12.length;
            var ClosureVar_16: scala.Int = 0;
            var ClosureVar_17: scala.Option[scala.collection.IndexedSeq[scala.Int]] = scala.None;
            var v_18: scala.Option[scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.MutVar[scala.Int]]]] = scala.None;
            envVar_5 = scala.Some.apply[scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.MutVar[scala.Int], scala.Tuple2[squid.lib.`package`.MutVar[scala.Option[scala.collection.IndexedSeq[scala.Int]]], squid.lib.`package`.MutVar[scala.Option[scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.MutVar[scala.Int]]]]]]]]]](scala.Tuple2.apply[scala.Int, scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.MutVar[scala.Int], scala.Tuple2[squid.lib.`package`.MutVar[scala.Option[scala.collection.IndexedSeq[scala.Int]]], squid.lib.`package`.MutVar[scala.Option[scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.MutVar[scala.Int]]]]]]]]](ClosureVar_14, scala.Tuple2.apply[scala.Int, scala.Tuple2[squid.lib.`package`.MutVar[scala.Int], scala.Tuple2[squid.lib.`package`.MutVar[scala.Option[scala.collection.IndexedSeq[scala.Int]]], squid.lib.`package`.MutVar[scala.Option[scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.MutVar[scala.Int]]]]]]]](ClosureVar_15, scala.Tuple2.apply[squid.lib.`package`.MutVar[scala.Int], scala.Tuple2[squid.lib.`package`.MutVar[scala.Option[scala.collection.IndexedSeq[scala.Int]]], squid.lib.`package`.MutVar[scala.Option[scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.MutVar[scala.Int]]]]]]](squid.lib.MutVarProxy[scala.Int](ClosureVar_16, ((a) => ClosureVar_16 = a)), scala.Tuple2.apply[squid.lib.`package`.MutVar[scala.Option[scala.collection.IndexedSeq[scala.Int]]], squid.lib.`package`.MutVar[scala.Option[scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.MutVar[scala.Int]]]]]](squid.lib.MutVarProxy[scala.Option[scala.collection.IndexedSeq[scala.Int]]](ClosureVar_17, ((a) => ClosureVar_17 = a)), squid.lib.MutVarProxy[scala.Option[scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.MutVar[scala.Int]]]]](v_18, ((a) => v_18 = a)))))));
            false
          })
        }) 
          ()
        ;
        val x_19 = i_3;
        x_19.==(x_2)
      }
    else
      ();
    val x_20 = envVar_5;
    if (x_20.isDefined.`unary_!`)
      completed_7 = true
    else
      {
        val x_21 = envVar_5;
        var completed_22: scala.Boolean = false;
        var continue_23: scala.Boolean = false;
        while ({
          val sch_24 = x_21.get._2;
          val sch_25 = sch_24._2;
          val sch_26 = sch_25._2;
          val sch_27 = sch_26._2;
          val lsch_28 = squid.utils.Lazy.apply[squid.lib.`package`.MutVar[scala.Option[scala.collection.IndexedSeq[scala.Int]]]](sch_26._1);
          val x_29 = sch_27.!;
          if (x_29.isDefined.`unary_!`)
            {
              val sch_30 = sch_25._1;
              val sch_31 = sch_24._1;
              while ({
                val x_32 = sch_30.!;
                x_32.<(sch_31).&&({
                  val x_33 = sch_30.!;
                  val x_34 = aVar_4;
                  val x_35 = x_34.get.apply(x_33);
                  val x_36 = sch_30.!;
                  sch_30.:=(x_36.+(1));
                  lsch_28.value.:=(scala.Some.apply[scala.collection.IndexedSeq[scala.Int]](x_35));
                  val ClosureVar_37 = x_35.size;
                  val ClosureVar_38 = x_35.length;
                  var v_39: scala.Int = 0;
                  sch_27.:=(scala.Some.apply[scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.MutVar[scala.Int]]]](scala.Tuple2.apply[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.MutVar[scala.Int]]](ClosureVar_37, scala.Tuple2.apply[scala.Int, squid.lib.`package`.MutVar[scala.Int]](ClosureVar_38, squid.lib.MutVarProxy[scala.Int](v_39, ((a) => v_39 = a))))));
                  false
                })
              }) 
                ()
              ;
              val x_40 = sch_30.!;
              x_40.==(sch_31)
            }
          else
            ();
          val x_41 = sch_27.!;
          if (x_41.isDefined.`unary_!`)
            completed_22 = true
          else
            {
              val x_42 = sch_27.!;
              val sch_43 = x_42.get._2;
              val sch_44 = sch_43._2;
              val sch_45 = sch_43._1;
              while ({
                val x_46 = sch_44.!;
                x_46.<(sch_45).&&({
                  val x_47 = sch_44.!;
                  val x_48 = lsch_28.value.!;
                  val x_49 = x_48.get.apply(x_47);
                  val x_50 = sch_44.!;
                  sch_44.:=(x_50.+(1));
                  val x_51 = cur_6;
                  cur_6 = x_51.+(x_49);
                  continue_8 = true;
                  val x_52 = continue_8;
                  continue_23 = x_52;
                  continue_23
                })
              }) 
                ()
              ;
              val x_53 = sch_44.!;
              if (x_53.==(sch_45))
                sch_27.:=(scala.None)
              else
                ()
            };
          val x_54 = completed_22;
          x_54.`unary_!`.&&(continue_23)
        }) 
          ()
        ;
        val x_55 = completed_22;
        if (x_55)
          envVar_5 = scala.None
        else
          ()
      };
    val x_56 = completed_7;
    x_56.`unary_!`.&&(continue_8)
  }) 
    ()
  ;
  completed_7;
  cur_6
})

// === LateImperative ===

// Transfo time: 0ms  Stringifying time: 112ms

// Same as above.

// === VarFlattening ===

// Transfo time: 171ms  Stringifying time: 122ms

((xs_0: scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]]]) => {
  val sch_1 = squid.lib.`package`.uncheckedNullValue[scala.Int];
  val x_2 = xs_0.size;
  val x_3 = xs_0.length;
  var i_4: scala.Int = 0;
  var isDefined_5: scala.Boolean = false;
  var optVal_6: scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]] = squid.lib.`package`.uncheckedNullValue[scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]]];
  var isDefined_7: scala.Boolean = false;
  var lhs_8: scala.Int = sch_1;
  var lhs_9: scala.Int = sch_1;
  var flatVar_10: scala.Int = sch_1;
  var flatVar_11: scala.Option[scala.collection.IndexedSeq[scala.Int]] = squid.lib.`package`.uncheckedNullValue[scala.Option[scala.collection.IndexedSeq[scala.Int]]];
  var rhs_12: squid.lib.`package`.MutVar[scala.Option[scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.MutVar[scala.Int]]]]] = squid.lib.`package`.uncheckedNullValue[squid.lib.`package`.MutVar[scala.Option[scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.MutVar[scala.Int]]]]]];
  var cur_13: scala.Int = 123;
  var completed_14: scala.Boolean = false;
  var continue_15: scala.Boolean = false;
  while ({
    val x_16 = isDefined_7;
    if (x_16.`unary_!`)
      {
        while ({
          val x_17 = i_4;
          x_17.<(x_3).&&({
            val x_18 = i_4;
            val x_19 = xs_0.apply(x_18);
            val x_20 = i_4;
            i_4 = x_20.+(1);
            optVal_6 = x_19;
            isDefined_5 = true;
            val ClosureVar_21 = x_19.size;
            val ClosureVar_22 = x_19.length;
            var ClosureVar_23: scala.Int = 0;
            var ClosureVar_24: scala.Option[scala.collection.IndexedSeq[scala.Int]] = scala.None;
            var v_25: scala.Option[scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.MutVar[scala.Int]]]] = scala.None;
            lhs_8 = ClosureVar_21;
            lhs_9 = ClosureVar_22;
            val x_26 = ClosureVar_23;
            flatVar_10 = x_26;
            val x_27 = ClosureVar_24;
            flatVar_11 = x_27;
            rhs_12 = squid.lib.MutVarProxy[scala.Option[scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.MutVar[scala.Int]]]]](v_25, ((a) => v_25 = a));
            isDefined_7 = true;
            false
          })
        }) 
          ()
        ;
        val x_28 = i_4;
        x_28.==(x_3)
      }
    else
      ();
    val x_29 = isDefined_7;
    if (x_29.`unary_!`)
      completed_14 = true
    else
      {
        var completed_30: scala.Boolean = false;
        var continue_31: scala.Boolean = false;
        while ({
          val x_32 = rhs_12;
          val x_33 = x_32.!;
          if (x_33.isDefined.`unary_!`)
            {
              while ({
                val x_34 = flatVar_10;
                val x_35 = lhs_9;
                x_34.<(x_35).&&({
                  val x_36 = flatVar_10;
                  val x_37 = optVal_6;
                  val x_38 = x_37.apply(x_36);
                  val x_39 = flatVar_10;
                  flatVar_10 = x_39.+(1);
                  flatVar_11 = scala.Some.apply[scala.collection.IndexedSeq[scala.Int]](x_38);
                  val ClosureVar_40 = x_38.size;
                  val ClosureVar_41 = x_38.length;
                  var v_42: scala.Int = 0;
                  val x_43 = rhs_12;
                  x_43.:=(scala.Some.apply[scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.MutVar[scala.Int]]]](scala.Tuple2.apply[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.MutVar[scala.Int]]](ClosureVar_40, scala.Tuple2.apply[scala.Int, squid.lib.`package`.MutVar[scala.Int]](ClosureVar_41, squid.lib.MutVarProxy[scala.Int](v_42, ((a) => v_42 = a))))));
                  false
                })
              }) 
                ()
              ;
              val x_44 = flatVar_10;
              val x_45 = lhs_9;
              x_44.==(x_45)
            }
          else
            ();
          val x_46 = rhs_12;
          val x_47 = x_46.!;
          if (x_47.isDefined.`unary_!`)
            completed_30 = true
          else
            {
              val x_48 = rhs_12;
              val x_49 = x_48.!;
              val sch_50 = x_49.get._2;
              val sch_51 = sch_50._2;
              val sch_52 = sch_50._1;
              while ({
                val x_53 = sch_51.!;
                x_53.<(sch_52).&&({
                  val x_54 = sch_51.!;
                  val x_55 = flatVar_11;
                  val x_56 = x_55.get.apply(x_54);
                  val x_57 = sch_51.!;
                  sch_51.:=(x_57.+(1));
                  val x_58 = cur_13;
                  cur_13 = x_58.+(x_56);
                  continue_15 = true;
                  val x_59 = continue_15;
                  continue_31 = x_59;
                  continue_31
                })
              }) 
                ()
              ;
              val x_60 = sch_51.!;
              if (x_60.==(sch_52))
                {
                  val x_61 = rhs_12;
                  x_61.:=(scala.None)
                }
              else
                ()
            };
          val x_62 = completed_30;
          x_62.`unary_!`.&&(continue_31)
        }) 
          ()
        ;
        val x_63 = completed_30;
        if (x_63)
          isDefined_7 = false
        else
          ()
      };
    val x_64 = completed_14;
    x_64.`unary_!`.&&(continue_15)
  }) 
    ()
  ;
  completed_14;
  cur_13
})

// === Low-Level Norm ===

// Transfo time: 40ms  Stringifying time: 130ms

((xs_0: scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]]]) => {
  val x_1 = xs_0.size;
  val x_2 = xs_0.length;
  var i_3: scala.Int = 0;
  var isDefined_4: scala.Boolean = false;
  var optVal_5: scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]] = null;
  var isDefined_6: scala.Boolean = false;
  var lhs_7: scala.Int = 0;
  var lhs_8: scala.Int = 0;
  var flatVar_9: scala.Int = 0;
  var flatVar_10: scala.Option[scala.collection.IndexedSeq[scala.Int]] = null;
  var rhs_11: squid.lib.`package`.MutVar[scala.Option[scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.MutVar[scala.Int]]]]] = null;
  var cur_12: scala.Int = 123;
  var completed_13: scala.Boolean = false;
  var continue_14: scala.Boolean = false;
  while ({
    val x_15 = isDefined_6;
    if (x_15)
      ()
    else
      {
        val x_16 = i_3;
        if (x_16.<(x_2))
          {
            val x_17 = i_3;
            val x_18 = xs_0.apply(x_17);
            val x_19 = i_3;
            i_3 = x_19.+(1);
            optVal_5 = x_18;
            isDefined_4 = true;
            val ClosureVar_20 = x_18.size;
            val ClosureVar_21 = x_18.length;
            var ClosureVar_22: scala.Int = 0;
            var ClosureVar_23: scala.Option[scala.collection.IndexedSeq[scala.Int]] = scala.None;
            var v_24: scala.Option[scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.MutVar[scala.Int]]]] = scala.None;
            lhs_7 = ClosureVar_20;
            lhs_8 = ClosureVar_21;
            val x_25 = ClosureVar_22;
            flatVar_9 = x_25;
            val x_26 = ClosureVar_23;
            flatVar_10 = x_26;
            rhs_11 = squid.lib.MutVarProxy[scala.Option[scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.MutVar[scala.Int]]]]](v_24, ((a) => v_24 = a));
            isDefined_6 = true
          }
        else
          ();
        val x_27 = i_3;
        x_27.==(x_2)
      };
    val x_28 = isDefined_6;
    if (x_28)
      {
        var completed_29: scala.Boolean = false;
        var continue_30: scala.Boolean = false;
        while ({
          val x_31 = rhs_11;
          val x_32 = x_31.!;
          if (x_32.isDefined)
            ()
          else
            {
              val x_33 = flatVar_9;
              val x_34 = lhs_8;
              if (x_33.<(x_34))
                {
                  val x_35 = flatVar_9;
                  val x_36 = optVal_5;
                  val x_37 = x_36.apply(x_35);
                  val x_38 = flatVar_9;
                  flatVar_9 = x_38.+(1);
                  flatVar_10 = scala.Some.apply[scala.collection.IndexedSeq[scala.Int]](x_37);
                  val ClosureVar_39 = x_37.size;
                  val ClosureVar_40 = x_37.length;
                  var v_41: scala.Int = 0;
                  val x_42 = rhs_11;
                  x_42.:=(scala.Some.apply[scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.MutVar[scala.Int]]]](scala.Tuple2.apply[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.MutVar[scala.Int]]](ClosureVar_39, scala.Tuple2.apply[scala.Int, squid.lib.`package`.MutVar[scala.Int]](ClosureVar_40, squid.lib.MutVarProxy[scala.Int](v_41, ((a) => v_41 = a))))))
                }
              else
                ();
              val x_43 = flatVar_9;
              val x_44 = lhs_8;
              x_43.==(x_44)
            };
          val x_45 = rhs_11;
          val x_46 = x_45.!;
          if (x_46.isDefined)
            {
              val x_47 = rhs_11;
              val x_48 = x_47.!;
              val sch_49 = x_48.get._2;
              val sch_50 = sch_49._2;
              val sch_51 = sch_49._1;
              while ({
                val x_52 = sch_50.!;
                x_52.<(sch_51).&&({
                  val x_53 = sch_50.!;
                  val x_54 = flatVar_10;
                  val x_55 = x_54.get.apply(x_53);
                  val x_56 = sch_50.!;
                  sch_50.:=(x_56.+(1));
                  val x_57 = cur_12;
                  cur_12 = x_57.+(x_55);
                  continue_14 = true;
                  val x_58 = continue_14;
                  continue_30 = x_58;
                  continue_30
                })
              }) 
                ()
              ;
              val x_59 = sch_50.!;
              if (x_59.==(sch_51))
                {
                  val x_60 = rhs_11;
                  x_60.:=(scala.None)
                }
              else
                ()
            }
          else
            completed_29 = true;
          val x_61 = completed_29;
          x_61.`unary_!`.&&(continue_30)
        }) 
          ()
        ;
        val x_62 = completed_29;
        if (x_62)
          isDefined_6 = false
        else
          ()
      }
    else
      completed_13 = true;
    val x_63 = completed_13;
    x_63.`unary_!`.&&(continue_14)
  }) 
    ()
  ;
  completed_13;
  cur_12
})

// === ReNorm (should be the same) ===

// Transfo time: 81ms  Stringifying time: 158ms

((xs_0: scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]]]) => {
  val x_1 = xs_0.size;
  val x_2 = xs_0.length;
  var i_3: scala.Int = 0;
  var isDefined_4: scala.Boolean = false;
  var optVal_5: scala.collection.IndexedSeq[scala.collection.IndexedSeq[scala.Int]] = null;
  var isDefined_6: scala.Boolean = false;
  var lhs_7: scala.Int = 0;
  var lhs_8: scala.Int = 0;
  var flatVar_9: scala.Int = 0;
  var flatVar_10: scala.Option[scala.collection.IndexedSeq[scala.Int]] = null;
  var rhs_11: squid.lib.`package`.MutVar[scala.Option[scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.MutVar[scala.Int]]]]] = null;
  var cur_12: scala.Int = 123;
  var completed_13: scala.Boolean = false;
  var continue_14: scala.Boolean = false;
  while ({
    val x_15 = isDefined_6;
    if (x_15)
      ()
    else
      {
        val x_16 = i_3;
        if (x_16.<(x_2))
          {
            val x_17 = i_3;
            val x_18 = xs_0.apply(x_17);
            val x_19 = i_3;
            i_3 = x_19.+(1);
            optVal_5 = x_18;
            isDefined_4 = true;
            val ClosureVar_20 = x_18.size;
            val ClosureVar_21 = x_18.length;
            var ClosureVar_22: scala.Int = 0;
            var ClosureVar_23: scala.Option[scala.collection.IndexedSeq[scala.Int]] = scala.None;
            var x_24: scala.Option[scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.MutVar[scala.Int]]]] = scala.None;
            lhs_7 = ClosureVar_20;
            lhs_8 = ClosureVar_21;
            val x_25 = ClosureVar_22;
            flatVar_9 = x_25;
            val x_26 = ClosureVar_23;
            flatVar_10 = x_26;
            rhs_11 = squid.lib.MutVarProxy[scala.Option[scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.MutVar[scala.Int]]]]](x_24, ((a) => x_24 = a));
            isDefined_6 = true
          }
        else
          ();
        val x_27 = i_3;
        x_27.==(x_2)
      };
    val x_28 = isDefined_6;
    if (x_28)
      {
        var completed_29: scala.Boolean = false;
        var continue_30: scala.Boolean = false;
        while ({
          val x_31 = rhs_11;
          val x_32 = x_31.!;
          if (x_32.isDefined)
            ()
          else
            {
              val x_33 = flatVar_9;
              val x_34 = lhs_8;
              if (x_33.<(x_34))
                {
                  val x_35 = flatVar_9;
                  val x_36 = optVal_5;
                  val x_37 = x_36.apply(x_35);
                  val x_38 = flatVar_9;
                  flatVar_9 = x_38.+(1);
                  flatVar_10 = scala.Some.apply[scala.collection.IndexedSeq[scala.Int]](x_37);
                  val ClosureVar_39 = x_37.size;
                  val ClosureVar_40 = x_37.length;
                  var x_41: scala.Int = 0;
                  val x_42 = rhs_11;
                  x_42.:=(scala.Some.apply[scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.MutVar[scala.Int]]]](scala.Tuple2.apply[scala.Int, scala.Tuple2[scala.Int, squid.lib.`package`.MutVar[scala.Int]]](ClosureVar_39, scala.Tuple2.apply[scala.Int, squid.lib.`package`.MutVar[scala.Int]](ClosureVar_40, squid.lib.MutVarProxy[scala.Int](x_41, ((a) => x_41 = a))))))
                }
              else
                ();
              val x_43 = flatVar_9;
              val x_44 = lhs_8;
              x_43.==(x_44)
            };
          val x_45 = rhs_11;
          val x_46 = x_45.!;
          if (x_46.isDefined)
            {
              val x_47 = rhs_11;
              val x_48 = x_47.!;
              val sch_49 = x_48.get._2;
              val sch_50 = sch_49._2;
              val sch_51 = sch_49._1;
              while ({
                val x_52 = sch_50.!;
                x_52.<(sch_51).&&({
                  val x_53 = sch_50.!;
                  val x_54 = flatVar_10;
                  val x_55 = x_54.get.apply(x_53);
                  val x_56 = sch_50.!;
                  sch_50.:=(x_56.+(1));
                  val x_57 = cur_12;
                  cur_12 = x_57.+(x_55);
                  continue_14 = true;
                  val x_58 = continue_14;
                  continue_30 = x_58;
                  continue_30
                })
              }) 
                ()
              ;
              val x_59 = sch_50.!;
              if (x_59.==(sch_51))
                {
                  val x_60 = rhs_11;
                  x_60.:=(scala.None)
                }
              else
                ()
            }
          else
            completed_29 = true;
          val x_61 = completed_29;
          x_61.`unary_!`.&&(continue_30)
        }) 
          ()
        ;
        val x_62 = completed_29;
        if (x_62)
          isDefined_6 = false
        else
          ()
      }
    else
      completed_13 = true;
    val x_63 = completed_13;
    x_63.`unary_!`.&&(continue_14)
  }) 
    ()
  ;
  completed_13;
  cur_12
})
