// Automatically-generated code

// === Init ===

// Transfo time: 0ms  Stringifying time: 25ms

((x$2_0: scala.collection.Iterable[java.lang.String]) => {
  val x_1 = sfusion.algo.`package`.joinLinesComplex$default$2;
  val x_3 = new sfusion.Sequence[java.lang.String]((() => {
    val x_2 = x$2_0.iterator;
    sfusion.impl.`package`.fromIterator[java.lang.String](x_2)
  }), scala.`package`.Right.apply[scala.Nothing, scala.Boolean](false));
  val x_12 = x_3.flatMap[scala.Char](((str_4: java.lang.String) => {
    val sch_5 = scala.`package`.Left;
    val x_6 = scala.Predef.wrapString(x_1);
    val x_7 = ((x_6): scala.collection.IndexedSeq[scala.Char]).size;
    val x_8 = new sfusion.Sequence[scala.Char]((() => sfusion.impl.`package`.fromIndexed[scala.Char](((x_6): scala.collection.IndexedSeq[scala.Char]))), sch_5.apply[scala.Int, scala.Nothing](x_7));
    val x_9 = scala.Predef.wrapString(str_4);
    val x_10 = ((x_9): scala.collection.IndexedSeq[scala.Char]).size;
    val x_11 = new sfusion.Sequence[scala.Char]((() => sfusion.impl.`package`.fromIndexed[scala.Char](((x_9): scala.collection.IndexedSeq[scala.Char]))), sch_5.apply[scala.Int, scala.Nothing](x_10));
    x_8.++[scala.Char](x_11)
  }));
  val x_13 = x_12.drop(x_1.length());
  x_13.fold[java.lang.String]("")(((x$10_14: java.lang.String, x$11_15: scala.Char) => {
    val x_16 = scala.Predef.augmentString(x$10_14);
    val x_17 = scala.Predef.StringCanBuildFrom;
    x_16.:+[scala.Char, java.lang.String](x$11_15)(x_17)
  }))
})

// === HL ===

// Transfo time: 0ms  Stringifying time: 6ms

// Same as above.

// === Impl ===

// Transfo time: 17ms  Stringifying time: 43ms

((x$2_0: scala.collection.Iterable[java.lang.String]) => {
  val sch_1 = scala.`package`.Right;
  val x_2 = sfusion.algo.`package`.joinLinesComplex$default$2;
  val x_4 = new sfusion.Sequence[java.lang.String]((() => {
    val x_3 = x$2_0.iterator;
    sfusion.impl.`package`.fromIterator[java.lang.String](x_3)
  }), sch_1.apply[scala.Nothing, scala.Boolean](false));
  val x_23 = new sfusion.Sequence[scala.Char]((() => {
    val x_5 = x_4.under;
    val x_6 = x_5.apply();
    sfusion.impl.`package`.flatMap[java.lang.String, scala.Char](x_6)(((x_7: java.lang.String) => {
      val sch_8 = scala.`package`.Left;
      val x_9 = scala.Predef.wrapString(x_2);
      val x_10 = ((x_9): scala.collection.IndexedSeq[scala.Char]).size;
      val x_11 = new sfusion.Sequence[scala.Char]((() => sfusion.impl.`package`.fromIndexed[scala.Char](((x_9): scala.collection.IndexedSeq[scala.Char]))), sch_8.apply[scala.Int, scala.Nothing](x_10));
      val x_12 = scala.Predef.wrapString(x_7);
      val x_13 = ((x_12): scala.collection.IndexedSeq[scala.Char]).size;
      val x_14 = new sfusion.Sequence[scala.Char]((() => sfusion.impl.`package`.fromIndexed[scala.Char](((x_12): scala.collection.IndexedSeq[scala.Char]))), sch_8.apply[scala.Int, scala.Nothing](x_13));
      val x_15 = x_11.size;
      val x_16 = x_14.size;
      val x_21 = new sfusion.Sequence[scala.Char]((() => {
        val x_17 = x_11.under;
        val x_18 = x_17.apply();
        val x_19 = x_14.under;
        val x_20 = x_19.apply();
        sfusion.impl.`package`.concat[scala.Char](x_18, x_20)
      }), sfusion.`package`.addSizes(x_15, x_16));
      val x_22 = x_21.under;
      x_22.apply()
    }))
  }), sch_1.apply[scala.Nothing, scala.Boolean](true));
  val x_24 = x_23.size;
  val x_27 = new sfusion.Sequence[scala.Char]((() => {
    val x_25 = x_23.under;
    val x_26 = x_25.apply();
    sfusion.impl.`package`.drop[scala.Char](x_26)(x_2.length())
  }), sfusion.`package`.minSize(x_24, scala.`package`.Left.apply[scala.Int, scala.Nothing](x_2.length())));
  val x_28 = x_27.under;
  val x_29 = x_28.apply();
  sfusion.impl.`package`.fold[scala.Char, java.lang.String](x_29)("")(((x$10_30: java.lang.String, x$11_31: scala.Char) => {
    val x_32 = scala.Predef.augmentString(x$10_30);
    val x_33 = scala.Predef.StringCanBuildFrom;
    x_32.:+[scala.Char, java.lang.String](x$11_31)(x_33)
  }))
})

// === CtorInline ===

// Transfo time: 14ms  Stringifying time: 18ms

((x$2_0: scala.collection.Iterable[java.lang.String]) => {
  val x_1 = sfusion.algo.`package`.joinLinesComplex$default$2;
  val x_2 = x$2_0.iterator;
  val x_3 = sfusion.impl.`package`.fromIterator[java.lang.String](x_2);
  val x_13 = sfusion.impl.`package`.flatMap[java.lang.String, scala.Char](x_3)(((x_4: java.lang.String) => {
    val x_5 = scala.Predef.wrapString(x_1);
    val sch_6 = ((x_5): scala.collection.IndexedSeq[scala.Char]);
    val x_7 = sch_6.size;
    val x_8 = scala.Predef.wrapString(x_4);
    val sch_9 = ((x_8): scala.collection.IndexedSeq[scala.Char]);
    val x_10 = sch_9.size;
    val x_11 = sfusion.impl.`package`.fromIndexed[scala.Char](sch_6);
    val x_12 = sfusion.impl.`package`.fromIndexed[scala.Char](sch_9);
    sfusion.impl.`package`.concat[scala.Char](x_11, x_12)
  }));
  val x_14 = sfusion.impl.`package`.drop[scala.Char](x_13)(x_1.length());
  sfusion.impl.`package`.fold[scala.Char, java.lang.String](x_14)("")(((x$10_15: java.lang.String, x$11_16: scala.Char) => {
    val x_17 = scala.Predef.augmentString(x$10_15);
    val x_18 = scala.Predef.StringCanBuildFrom;
    x_17.:+[scala.Char, java.lang.String](x$11_16)(x_18)
  }))
})

// === ImplOptim ===

// Transfo time: 0ms  Stringifying time: 4ms

// Same as above.

// === Imperative ===

// Transfo time: 23ms  Stringifying time: 69ms

((x$2_0: scala.collection.Iterable[java.lang.String]) => {
  val x_1 = sfusion.algo.`package`.joinLinesComplex$default$2;
  val x_2 = x$2_0.iterator;
  val x_37 = sfusion.impl.`package`.flatMap[java.lang.String, scala.Char](((k_3: scala.Function1[java.lang.String, scala.Boolean]) => {
    while ({
      val x_4 = x_2.hasNext;
      x_4.&&({
        val x_5 = x_2.next();
        k_3(x_5)
      })
    }) 
      ()
    ;
    val x_6 = x_2.hasNext;
    x_6.`unary_!`
  }))(((x_7: java.lang.String) => {
    val x_8 = scala.Predef.wrapString(x_1);
    val x_9 = ((x_8): scala.collection.IndexedSeq[scala.Char]).size;
    val x_10 = scala.Predef.wrapString(x_7);
    val x_11 = ((x_10): scala.collection.IndexedSeq[scala.Char]).size;
    val x_12 = ((x_8): scala.collection.IndexedSeq[scala.Char]).length;
    var i_13: scala.Int = 0;
    val x_14 = ((x_10): scala.collection.IndexedSeq[scala.Char]).length;
    var i_15: scala.Int = 0;
    var curIsLhs_16: scala.Boolean = true;
    ((k_17: scala.Function1[scala.Char, scala.Boolean]) => {
      var cont_18: scala.Boolean = true;
      var finished_19: scala.Boolean = false;
      while ({
        val x_20 = cont_18;
        x_20.&&({
          val x_21 = finished_19;
          x_21.`unary_!`
        })
      }) 
        {
          var next_22: scala.Option[scala.Char] = scala.None;
          val x_23 = curIsLhs_16;
          if (x_23)
            {
              while ({
                val x_24 = i_13;
                x_24.<(x_12).&&({
                  val x_25 = i_13;
                  val x_26 = ((x_8): scala.collection.IndexedSeq[scala.Char]).apply(x_25);
                  val x_27 = i_13;
                  i_13 = x_27.+(1);
                  next_22 = scala.Some.apply[scala.Char](x_26);
                  false
                })
              }) 
                ()
              ;
              val x_28 = i_13;
              if (x_28.==(x_12))
                curIsLhs_16 = false
              else
                ()
            }
          else
            ();
          val x_29 = next_22;
          if (x_29.isDefined.`unary_!`)
            {
              while ({
                val x_30 = i_15;
                x_30.<(x_14).&&({
                  val x_31 = i_15;
                  val x_32 = ((x_10): scala.collection.IndexedSeq[scala.Char]).apply(x_31);
                  val x_33 = i_15;
                  i_15 = x_33.+(1);
                  next_22 = scala.Some.apply[scala.Char](x_32);
                  false
                })
              }) 
                ()
              ;
              val x_34 = i_15;
              if (x_34.==(x_14))
                finished_19 = true
              else
                ()
            }
          else
            ();
          val x_35 = next_22;
          if (x_35.isDefined)
            {
              val x_36 = k_17(x_35.get);
              cont_18 = x_36
            }
          else
            finished_19 = true
        }
      ;
      finished_19
    })
  }));
  var dropped_38: scala.Int = 0;
  var cur_39: java.lang.String = "";
  x_37(((a_40: scala.Char) => {
    val x_41 = dropped_38;
    if (x_41.<(x_1.length()))
      {
        val x_42 = dropped_38;
        dropped_38 = x_42.+(1);
        true
      }
    else
      {
        val x_43 = cur_39;
        val x_44 = scala.Predef.augmentString(x_43);
        val x_45 = scala.Predef.StringCanBuildFrom;
        val x_46 = x_44.:+[scala.Char, java.lang.String](a_40)(x_45);
        cur_39 = x_46;
        true
      }
  }));
  cur_39
})

// === FlatMapFusion ===

// Transfo time: 345ms  Stringifying time: 166ms

((x$2_0: scala.collection.Iterable[java.lang.String]) => {
  val x_1 = sfusion.algo.`package`.joinLinesComplex$default$2;
  val x_2 = x$2_0.iterator;
  var aVar_3: scala.Option[java.lang.String] = scala.None;
  var envVar_4: scala.Option[scala.Tuple2[scala.collection.immutable.WrappedString, scala.Tuple2[scala.Int, scala.Tuple2[scala.collection.immutable.WrappedString, scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.Var[scala.Int], scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.Var[scala.Int], squid.lib.`package`.Var[scala.Boolean]]]]]]]]]] = scala.None;
  var dropped_5: scala.Int = 0;
  var cur_6: java.lang.String = "";
  var completed_7: scala.Boolean = false;
  var continue_8: scala.Boolean = false;
  while ({
    val x_9 = envVar_4;
    if (x_9.isDefined.`unary_!`)
      {
        while ({
          val x_10 = x_2.hasNext;
          x_10.&&({
            val x_11 = x_2.next();
            aVar_3 = scala.Some.apply[java.lang.String](x_11);
            val ClosureVar_12 = scala.Predef.wrapString(x_1);
            val sch_13 = ((ClosureVar_12): scala.collection.IndexedSeq[scala.Char]);
            val ClosureVar_14 = sch_13.size;
            val ClosureVar_15 = scala.Predef.wrapString(x_11);
            val sch_16 = ((ClosureVar_15): scala.collection.IndexedSeq[scala.Char]);
            val ClosureVar_17 = sch_16.size;
            val ClosureVar_18 = sch_13.length;
            var ClosureVar_19: scala.Int = 0;
            val ClosureVar_20 = sch_16.length;
            var ClosureVar_21: scala.Int = 0;
            var v_22: scala.Boolean = true;
            envVar_4 = scala.Some.apply[scala.Tuple2[scala.collection.immutable.WrappedString, scala.Tuple2[scala.Int, scala.Tuple2[scala.collection.immutable.WrappedString, scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.Var[scala.Int], scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.Var[scala.Int], squid.lib.`package`.Var[scala.Boolean]]]]]]]]]](scala.Tuple2.apply[scala.collection.immutable.WrappedString, scala.Tuple2[scala.Int, scala.Tuple2[scala.collection.immutable.WrappedString, scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.Var[scala.Int], scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.Var[scala.Int], squid.lib.`package`.Var[scala.Boolean]]]]]]]]](ClosureVar_12, scala.Tuple2.apply[scala.Int, scala.Tuple2[scala.collection.immutable.WrappedString, scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.Var[scala.Int], scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.Var[scala.Int], squid.lib.`package`.Var[scala.Boolean]]]]]]]](ClosureVar_14, scala.Tuple2.apply[scala.collection.immutable.WrappedString, scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.Var[scala.Int], scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.Var[scala.Int], squid.lib.`package`.Var[scala.Boolean]]]]]]](ClosureVar_15, scala.Tuple2.apply[scala.Int, scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.Var[scala.Int], scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.Var[scala.Int], squid.lib.`package`.Var[scala.Boolean]]]]]](ClosureVar_17, scala.Tuple2.apply[scala.Int, scala.Tuple2[squid.lib.`package`.Var[scala.Int], scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.Var[scala.Int], squid.lib.`package`.Var[scala.Boolean]]]]](ClosureVar_18, scala.Tuple2.apply[squid.lib.`package`.Var[scala.Int], scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.Var[scala.Int], squid.lib.`package`.Var[scala.Boolean]]]](new squid.lib.VarProxy[scala.Int](ClosureVar_19, ((a) => ClosureVar_19 = a)), scala.Tuple2.apply[scala.Int, scala.Tuple2[squid.lib.`package`.Var[scala.Int], squid.lib.`package`.Var[scala.Boolean]]](ClosureVar_20, scala.Tuple2.apply[squid.lib.`package`.Var[scala.Int], squid.lib.`package`.Var[scala.Boolean]](new squid.lib.VarProxy[scala.Int](ClosureVar_21, ((a) => ClosureVar_21 = a)), new squid.lib.VarProxy[scala.Boolean](v_22, ((a) => v_22 = a)))))))))));
            false
          })
        }) 
          ()
        ;
        val x_23 = x_2.hasNext;
        x_23.`unary_!`
      }
    else
      ();
    val x_24 = envVar_4;
    if (x_24.isDefined.`unary_!`)
      completed_7 = true
    else
      {
        val x_25 = envVar_4;
        var cont_26: scala.Boolean = true;
        var finished_27: scala.Boolean = false;
        while ({
          val x_28 = cont_26;
          x_28.&&({
            val x_29 = finished_27;
            x_29.`unary_!`
          })
        }) 
          {
            var next_30: scala.Option[scala.Char] = scala.None;
            val x_31 = x_25.get._2._2._2._2._2._2._2._2.!;
            if (x_31)
              {
                while ({
                  val x_32 = x_25.get._2._2._2._2._2._1.!;
                  x_32.<(x_25.get._2._2._2._2._1).&&({
                    val sch_33 = x_25.get;
                    val sch_34 = sch_33._2;
                    val sch_35 = sch_34._2;
                    val sch_36 = sch_35._2;
                    val sch_37 = sch_36._2;
                    val sch_38 = sch_37._2;
                    val sch_39 = sch_38._1;
                    val x_40 = sch_39.!;
                    val x_41 = ((sch_33._1): scala.collection.IndexedSeq[scala.Char]).apply(x_40);
                    val x_42 = sch_39.!;
                    sch_39.:=(x_42.+(1));
                    next_30 = scala.Some.apply[scala.Char](x_41);
                    false
                  })
                }) 
                  ()
                ;
                val x_43 = x_25.get._2._2._2._2._2._1.!;
                if (x_43.==(x_25.get._2._2._2._2._1))
                  x_25.get._2._2._2._2._2._2._2._2.:=(false)
                else
                  ()
              }
            else
              ();
            val x_44 = next_30;
            if (x_44.isDefined.`unary_!`)
              {
                while ({
                  val x_45 = x_25.get._2._2._2._2._2._2._2._1.!;
                  x_45.<(x_25.get._2._2._2._2._2._2._1).&&({
                    val sch_46 = x_25.get;
                    val sch_47 = sch_46._2;
                    val sch_48 = sch_47._2;
                    val sch_49 = sch_48._2;
                    val sch_50 = sch_49._2;
                    val sch_51 = sch_50._2;
                    val sch_52 = sch_51._2;
                    val sch_53 = sch_52._2;
                    val sch_54 = sch_53._1;
                    val x_55 = sch_54.!;
                    val x_56 = ((sch_48._1): scala.collection.IndexedSeq[scala.Char]).apply(x_55);
                    val x_57 = sch_54.!;
                    sch_54.:=(x_57.+(1));
                    next_30 = scala.Some.apply[scala.Char](x_56);
                    false
                  })
                }) 
                  ()
                ;
                val sch_58 = x_25.get;
                val sch_59 = sch_58._2;
                val sch_60 = sch_59._2;
                val sch_61 = sch_60._2;
                val sch_62 = sch_61._2;
                val sch_63 = sch_62._2;
                val sch_64 = sch_63._2;
                val x_65 = sch_64._2._1.!;
                if (x_65.==(sch_64._1))
                  finished_27 = true
                else
                  ()
              }
            else
              ();
            val x_66 = next_30;
            if (x_66.isDefined)
              {
                val x_67 = dropped_5;
                val x_73 = if (x_67.<(x_1.length()))
                  {
                    val x_68 = dropped_5;
                    dropped_5 = x_68.+(1);
                    true
                  }
                else
                  {
                    val x_69 = cur_6;
                    val x_70 = scala.Predef.augmentString(x_69);
                    val x_71 = scala.Predef.StringCanBuildFrom;
                    val x_72 = x_70.:+[scala.Char, java.lang.String](x_66.get)(x_71);
                    cur_6 = x_72;
                    true
                  };
                continue_8 = x_73;
                val x_74 = continue_8;
                cont_26 = x_74
              }
            else
              finished_27 = true
          }
        ;
        val x_75 = finished_27;
        if (x_75)
          envVar_4 = scala.None
        else
          ()
      };
    val x_76 = completed_7;
    x_76.`unary_!`.&&(continue_8)
  }) 
    ()
  ;
  completed_7;
  cur_6
})

// === LateImperative ===

// Transfo time: 0ms  Stringifying time: 87ms

// Same as above.

// === VarFlattening ===

// Transfo time: 674ms  Stringifying time: 99ms

((x$2_0: scala.collection.Iterable[java.lang.String]) => {
  val sch_1 = squid.lib.`package`.uncheckedNullValue[scala.Int];
  val sch_2 = squid.lib.`package`.uncheckedNullValue[scala.collection.immutable.WrappedString];
  val x_3 = sfusion.algo.`package`.joinLinesComplex$default$2;
  val x_4 = x$2_0.iterator;
  var isDefined_5: scala.Boolean = false;
  var optVal_6: java.lang.String = squid.lib.`package`.uncheckedNullValue[java.lang.String];
  var isDefined_7: scala.Boolean = false;
  var lhs_8: scala.collection.immutable.WrappedString = sch_2;
  var lhs_9: scala.Int = sch_1;
  var lhs_10: scala.collection.immutable.WrappedString = sch_2;
  var lhs_11: scala.Int = sch_1;
  var lhs_12: scala.Int = sch_1;
  var flatVar_13: scala.Int = sch_1;
  var lhs_14: scala.Int = sch_1;
  var flatVar_15: scala.Int = sch_1;
  var flatVar_16: scala.Boolean = squid.lib.`package`.uncheckedNullValue[scala.Boolean];
  var dropped_17: scala.Int = 0;
  var cur_18: java.lang.String = "";
  var completed_19: scala.Boolean = false;
  var continue_20: scala.Boolean = false;
  while ({
    val x_21 = isDefined_7;
    if (x_21.`unary_!`)
      {
        while ({
          val x_22 = x_4.hasNext;
          x_22.&&({
            val x_23 = x_4.next();
            optVal_6 = x_23;
            isDefined_5 = true;
            val ClosureVar_24 = scala.Predef.wrapString(x_3);
            val sch_25 = ((ClosureVar_24): scala.collection.IndexedSeq[scala.Char]);
            val ClosureVar_26 = sch_25.size;
            val ClosureVar_27 = scala.Predef.wrapString(x_23);
            val sch_28 = ((ClosureVar_27): scala.collection.IndexedSeq[scala.Char]);
            val ClosureVar_29 = sch_28.size;
            val ClosureVar_30 = sch_25.length;
            var ClosureVar_31: scala.Int = 0;
            val ClosureVar_32 = sch_28.length;
            var ClosureVar_33: scala.Int = 0;
            var v_34: scala.Boolean = true;
            lhs_8 = ClosureVar_24;
            lhs_9 = ClosureVar_26;
            lhs_10 = ClosureVar_27;
            lhs_11 = ClosureVar_29;
            lhs_12 = ClosureVar_30;
            val x_35 = ClosureVar_31;
            flatVar_13 = x_35;
            lhs_14 = ClosureVar_32;
            val x_36 = ClosureVar_33;
            flatVar_15 = x_36;
            val x_37 = v_34;
            flatVar_16 = x_37;
            isDefined_7 = true;
            false
          })
        }) 
          ()
        ;
        val x_38 = x_4.hasNext;
        x_38.`unary_!`
      }
    else
      ();
    val x_39 = isDefined_7;
    if (x_39.`unary_!`)
      completed_19 = true
    else
      {
        var cont_40: scala.Boolean = true;
        var finished_41: scala.Boolean = false;
        while ({
          val x_42 = cont_40;
          x_42.&&({
            val x_43 = finished_41;
            x_43.`unary_!`
          })
        }) 
          {
            var isDefined_44: scala.Boolean = false;
            var optVal_45: scala.Char = squid.lib.`package`.uncheckedNullValue[scala.Char];
            val x_46 = flatVar_16;
            if (x_46)
              {
                while ({
                  val x_47 = flatVar_13;
                  val x_48 = lhs_12;
                  x_47.<(x_48).&&({
                    val x_49 = flatVar_13;
                    val x_50 = lhs_8;
                    val x_51 = x_50.apply(x_49);
                    val x_52 = flatVar_13;
                    flatVar_13 = x_52.+(1);
                    optVal_45 = x_51;
                    isDefined_44 = true;
                    false
                  })
                }) 
                  ()
                ;
                val x_53 = flatVar_13;
                val x_54 = lhs_12;
                if (x_53.==(x_54))
                  flatVar_16 = false
                else
                  ()
              }
            else
              ();
            val x_55 = isDefined_44;
            if (x_55.`unary_!`)
              {
                while ({
                  val x_56 = flatVar_15;
                  val x_57 = lhs_14;
                  x_56.<(x_57).&&({
                    val x_58 = flatVar_15;
                    val x_59 = lhs_10;
                    val x_60 = x_59.apply(x_58);
                    val x_61 = flatVar_15;
                    flatVar_15 = x_61.+(1);
                    optVal_45 = x_60;
                    isDefined_44 = true;
                    false
                  })
                }) 
                  ()
                ;
                val x_62 = flatVar_15;
                val x_63 = lhs_14;
                if (x_62.==(x_63))
                  finished_41 = true
                else
                  ()
              }
            else
              ();
            val x_64 = isDefined_44;
            if (x_64)
              {
                val x_65 = dropped_17;
                val x_72 = if (x_65.<(x_3.length()))
                  {
                    val x_66 = dropped_17;
                    dropped_17 = x_66.+(1);
                    true
                  }
                else
                  {
                    val x_67 = cur_18;
                    val x_68 = scala.Predef.augmentString(x_67);
                    val x_69 = scala.Predef.StringCanBuildFrom;
                    val x_70 = optVal_45;
                    val x_71 = x_68.:+[scala.Char, java.lang.String](x_70)(x_69);
                    cur_18 = x_71;
                    true
                  };
                continue_20 = x_72;
                val x_73 = continue_20;
                cont_40 = x_73
              }
            else
              finished_41 = true
          }
        ;
        val x_74 = finished_41;
        if (x_74)
          isDefined_7 = false
        else
          ()
      };
    val x_75 = completed_19;
    x_75.`unary_!`.&&(continue_20)
  }) 
    ()
  ;
  completed_19;
  cur_18
})

// === Low-Level Norm ===

// Transfo time: 179ms  Stringifying time: 98ms

((x$2_0: scala.collection.Iterable[java.lang.String]) => {
  val sch_1 = ((null): scala.collection.immutable.WrappedString);
  val x_2 = sfusion.algo.`package`.joinLinesComplex$default$2;
  val x_3 = x$2_0.iterator;
  var isDefined_4: scala.Boolean = false;
  var optVal_5: java.lang.String = null;
  var isDefined_6: scala.Boolean = false;
  var lhs_7: scala.collection.immutable.WrappedString = null;
  var lhs_8: scala.Int = 0;
  var lhs_9: scala.collection.immutable.WrappedString = null;
  var lhs_10: scala.Int = 0;
  var lhs_11: scala.Int = 0;
  var flatVar_12: scala.Int = 0;
  var lhs_13: scala.Int = 0;
  var flatVar_14: scala.Int = 0;
  var flatVar_15: scala.Boolean = false;
  var dropped_16: scala.Int = 0;
  var cur_17: java.lang.String = "";
  var completed_18: scala.Boolean = false;
  var continue_19: scala.Boolean = false;
  while ({
    val x_20 = isDefined_6;
    if (x_20)
      ()
    else
      {
        val x_21 = x_3.hasNext;
        if (x_21)
          {
            val x_22 = x_3.next();
            optVal_5 = x_22;
            isDefined_4 = true;
            val ClosureVar_23 = scala.Predef.wrapString(x_2);
            val sch_24 = ((ClosureVar_23): scala.collection.IndexedSeq[scala.Char]);
            val ClosureVar_25 = sch_24.size;
            val ClosureVar_26 = scala.Predef.wrapString(x_22);
            val sch_27 = ((ClosureVar_26): scala.collection.IndexedSeq[scala.Char]);
            val ClosureVar_28 = sch_27.size;
            val ClosureVar_29 = sch_24.length;
            var ClosureVar_30: scala.Int = 0;
            val ClosureVar_31 = sch_27.length;
            var ClosureVar_32: scala.Int = 0;
            var v_33: scala.Boolean = true;
            lhs_7 = ClosureVar_23;
            lhs_8 = ClosureVar_25;
            lhs_9 = ClosureVar_26;
            lhs_10 = ClosureVar_28;
            lhs_11 = ClosureVar_29;
            val x_34 = ClosureVar_30;
            flatVar_12 = x_34;
            lhs_13 = ClosureVar_31;
            val x_35 = ClosureVar_32;
            flatVar_14 = x_35;
            val x_36 = v_33;
            flatVar_15 = x_36;
            isDefined_6 = true
          }
        else
          ();
        val x_37 = x_3.hasNext;
        x_37.`unary_!`
      };
    val x_38 = isDefined_6;
    if (x_38)
      {
        var cont_39: scala.Boolean = true;
        var finished_40: scala.Boolean = false;
        while ({
          val x_41 = cont_39;
          x_41.&&({
            val x_42 = finished_40;
            x_42.`unary_!`
          })
        }) 
          {
            var isDefined_43: scala.Boolean = false;
            var optVal_44: scala.Char = '\00';
            val x_45 = flatVar_15;
            if (x_45)
              {
                val x_46 = flatVar_12;
                val x_47 = lhs_11;
                if (x_46.<(x_47))
                  {
                    val x_48 = flatVar_12;
                    val x_49 = lhs_7;
                    val x_50 = x_49.apply(x_48);
                    val x_51 = flatVar_12;
                    flatVar_12 = x_51.+(1);
                    optVal_44 = x_50;
                    isDefined_43 = true
                  }
                else
                  ();
                val x_52 = flatVar_12;
                val x_53 = lhs_11;
                if (x_52.==(x_53))
                  flatVar_15 = false
                else
                  ()
              }
            else
              ();
            val x_54 = isDefined_43;
            if (x_54)
              ()
            else
              {
                val x_55 = flatVar_14;
                val x_56 = lhs_13;
                if (x_55.<(x_56))
                  {
                    val x_57 = flatVar_14;
                    val x_58 = lhs_9;
                    val x_59 = x_58.apply(x_57);
                    val x_60 = flatVar_14;
                    flatVar_14 = x_60.+(1);
                    optVal_44 = x_59;
                    isDefined_43 = true
                  }
                else
                  ();
                val x_61 = flatVar_14;
                val x_62 = lhs_13;
                if (x_61.==(x_62))
                  finished_40 = true
                else
                  ()
              };
            val x_63 = isDefined_43;
            if (x_63)
              {
                val x_64 = dropped_16;
                if (x_64.<(x_2.length()))
                  {
                    val x_65 = dropped_16;
                    dropped_16 = x_65.+(1)
                  }
                else
                  ();
                val x_73 = x_64.<(x_2.length()).`unary_!`.&&({
                  val sch_66 = x_2.length();
                  val sch_67 = x_64.<(sch_66);
                  if (sch_67)
                    ()
                  else
                    {
                      val x_68 = cur_17;
                      val x_69 = scala.Predef.augmentString(x_68);
                      val x_70 = scala.Predef.StringCanBuildFrom;
                      val x_71 = optVal_44;
                      val x_72 = x_69.:+[scala.Char, java.lang.String](x_71)(x_70);
                      cur_17 = x_72
                    };
                  sch_67
                });
                continue_19 = x_73.`unary_!`;
                val x_74 = continue_19;
                cont_39 = x_74
              }
            else
              finished_40 = true
          }
        ;
        val x_75 = finished_40;
        if (x_75)
          isDefined_6 = false
        else
          ()
      }
    else
      completed_18 = true;
    val x_76 = completed_18;
    x_76.`unary_!`.&&(continue_19)
  }) 
    ()
  ;
  completed_18;
  cur_17
})

// === ReNorm (should be the same) ===

// Transfo time: 20ms  Stringifying time: 80ms

// Same as above.
