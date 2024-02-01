// Automatically-generated code

// === Init ===

// Transfo time: 0ms  Stringifying time: 35ms

((x$2_0: scala.collection.Iterable[java.lang.String]) => {
  val x_1 = sfusion.algo.`package`.joinLinesComplex$default$2;
  val x_3 = new sfusion.Sequence[java.lang.String]((() => {
    val x_2 = x$2_0.iterator;
    sfusion.impl.`package`.fromIterator[java.lang.String](x_2)
  }), scala.`package`.Right.apply[scala.Nothing, scala.Boolean](false));
  val x_14 = x_3.flatMap[scala.Char](((str_4: java.lang.String) => {
    val sch_5 = scala.`package`.Left;
    val x_6 = scala.Predef.wrapString(x_1);
    val sch_7 = ((x_6): scala.collection.IndexedSeq[scala.Char]);
    val x_8 = sch_7.size;
    val x_9 = new sfusion.Sequence[scala.Char]((() => sfusion.impl.`package`.fromIndexed[scala.Char](sch_7)), sch_5.apply[scala.Int, scala.Nothing](x_8));
    val x_10 = scala.Predef.wrapString(str_4);
    val sch_11 = ((x_10): scala.collection.IndexedSeq[scala.Char]);
    val x_12 = sch_11.size;
    val x_13 = new sfusion.Sequence[scala.Char]((() => sfusion.impl.`package`.fromIndexed[scala.Char](sch_11)), sch_5.apply[scala.Int, scala.Nothing](x_12));
    x_9.++[scala.Char](x_13)
  }));
  val x_15 = x_14.drop(x_1.length());
  x_15.fold[java.lang.String]("")(((x$10_16: java.lang.String, x$11_17: scala.Char) => {
    val x_18 = scala.Predef.augmentString(x$10_16);
    x_18.:+[scala.Char, java.lang.String](x$11_17)(scala.Predef.StringCanBuildFrom)
  }))
})

// === HL ===

// Transfo time: 0ms  Stringifying time: 8ms

// Same as above.

// === Impl ===

// Transfo time: 17ms  Stringifying time: 87ms

((x$2_0: scala.collection.Iterable[java.lang.String]) => {
  val sch_1 = scala.`package`.Left;
  val sch_2 = scala.`package`.Right;
  val x_3 = sfusion.algo.`package`.joinLinesComplex$default$2;
  val sch_4 = x_3.length();
  val x_6 = new sfusion.Sequence[java.lang.String]((() => {
    val x_5 = x$2_0.iterator;
    sfusion.impl.`package`.fromIterator[java.lang.String](x_5)
  }), sch_2.apply[scala.Nothing, scala.Boolean](false));
  val x_26 = new sfusion.Sequence[scala.Char]((() => {
    val x_7 = x_6.under;
    val x_8 = x_7.apply();
    sfusion.impl.`package`.flatMap[java.lang.String, scala.Char](x_8)(((x_9: java.lang.String) => {
      val x_10 = scala.Predef.wrapString(x_3);
      val sch_11 = ((x_10): scala.collection.IndexedSeq[scala.Char]);
      val x_12 = sch_11.size;
      val x_13 = new sfusion.Sequence[scala.Char]((() => sfusion.impl.`package`.fromIndexed[scala.Char](sch_11)), sch_1.apply[scala.Int, scala.Nothing](x_12));
      val x_14 = scala.Predef.wrapString(x_9);
      val sch_15 = ((x_14): scala.collection.IndexedSeq[scala.Char]);
      val x_16 = sch_15.size;
      val x_17 = new sfusion.Sequence[scala.Char]((() => sfusion.impl.`package`.fromIndexed[scala.Char](sch_15)), sch_1.apply[scala.Int, scala.Nothing](x_16));
      val x_18 = x_13.size;
      val x_19 = x_17.size;
      val x_24 = new sfusion.Sequence[scala.Char]((() => {
        val x_20 = x_13.under;
        val x_21 = x_20.apply();
        val x_22 = x_17.under;
        val x_23 = x_22.apply();
        sfusion.impl.`package`.concat[scala.Char](x_21, x_23)
      }), sfusion.`package`.addSizes(x_18, x_19));
      val x_25 = x_24.under;
      x_25.apply()
    }))
  }), sch_2.apply[scala.Nothing, scala.Boolean](true));
  val x_27 = x_26.size;
  val x_30 = new sfusion.Sequence[scala.Char]((() => {
    val x_28 = x_26.under;
    val x_29 = x_28.apply();
    sfusion.impl.`package`.drop[scala.Char](x_29)(sch_4)
  }), sfusion.`package`.minSize(x_27, sch_1.apply[scala.Int, scala.Nothing](sch_4)));
  val x_31 = x_30.under;
  val x_32 = x_31.apply();
  sfusion.impl.`package`.fold[scala.Char, java.lang.String](x_32)("")(((x$10_33: java.lang.String, x$11_34: scala.Char) => {
    val x_35 = scala.Predef.augmentString(x$10_33);
    x_35.:+[scala.Char, java.lang.String](x$11_34)(scala.Predef.StringCanBuildFrom)
  }))
})

// === CtorInline ===

// Transfo time: 11ms  Stringifying time: 30ms

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
    x_17.:+[scala.Char, java.lang.String](x$11_16)(scala.Predef.StringCanBuildFrom)
  }))
})

// === ImplOptim ===

// Transfo time: 0ms  Stringifying time: 5ms

// Same as above.

// === Imperative ===

// Transfo time: 23ms  Stringifying time: 91ms

((x$2_0: scala.collection.Iterable[java.lang.String]) => {
  val x_1 = sfusion.algo.`package`.joinLinesComplex$default$2;
  val x_2 = x$2_0.iterator;
  val x_39 = sfusion.impl.`package`.flatMap[java.lang.String, scala.Char](((k_3: scala.Function1[java.lang.String, scala.Boolean]) => {
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
    val sch_9 = ((x_8): scala.collection.IndexedSeq[scala.Char]);
    val x_10 = sch_9.size;
    val x_11 = scala.Predef.wrapString(x_7);
    val sch_12 = ((x_11): scala.collection.IndexedSeq[scala.Char]);
    val x_13 = sch_12.size;
    val x_14 = sch_9.length;
    var i_15: scala.Int = 0;
    val x_16 = sch_12.length;
    var i_17: scala.Int = 0;
    var curIsLhs_18: scala.Boolean = true;
    ((k_19: scala.Function1[scala.Char, scala.Boolean]) => {
      var cont_20: scala.Boolean = true;
      var finished_21: scala.Boolean = false;
      while ({
        val x_22 = cont_20;
        x_22.&&({
          val x_23 = finished_21;
          x_23.`unary_!`
        })
      }) 
        {
          var next_24: scala.Option[scala.Char] = scala.None;
          val x_25 = curIsLhs_18;
          if (x_25)
            {
              while ({
                val x_26 = i_15;
                x_26.<(x_14).&&({
                  val x_27 = i_15;
                  val x_28 = sch_9.apply(x_27);
                  val x_29 = i_15;
                  i_15 = x_29.+(1);
                  next_24 = scala.Some.apply[scala.Char](x_28);
                  false
                })
              }) 
                ()
              ;
              val x_30 = i_15;
              if (x_30.==(x_14))
                curIsLhs_18 = false
              else
                ()
            }
          else
            ();
          val x_31 = next_24;
          if (x_31.isDefined.`unary_!`)
            {
              while ({
                val x_32 = i_17;
                x_32.<(x_16).&&({
                  val x_33 = i_17;
                  val x_34 = sch_12.apply(x_33);
                  val x_35 = i_17;
                  i_17 = x_35.+(1);
                  next_24 = scala.Some.apply[scala.Char](x_34);
                  false
                })
              }) 
                ()
              ;
              val x_36 = i_17;
              if (x_36.==(x_16))
                finished_21 = true
              else
                ()
            }
          else
            ();
          val x_37 = next_24;
          if (x_37.isDefined)
            {
              val x_38 = k_19(x_37.get);
              cont_20 = x_38
            }
          else
            finished_21 = true
        }
      ;
      finished_21
    })
  }));
  var dropped_40: scala.Int = 0;
  var cur_41: java.lang.String = "";
  x_39(((a_42: scala.Char) => {
    val x_43 = dropped_40;
    if (x_43.<(x_1.length()))
      {
        val x_44 = dropped_40;
        dropped_40 = x_44.+(1);
        true
      }
    else
      {
        val x_45 = cur_41;
        val x_46 = scala.Predef.augmentString(x_45);
        val x_47 = x_46.:+[scala.Char, java.lang.String](a_42)(scala.Predef.StringCanBuildFrom);
        cur_41 = x_47;
        true
      }
  }));
  cur_41
})

// === FlatMapFusion ===

// Transfo time: 162ms  Stringifying time: 153ms

((x$2_0: scala.collection.Iterable[java.lang.String]) => {
  val x_1 = sfusion.algo.`package`.joinLinesComplex$default$2;
  val x_2 = x$2_0.iterator;
  var aVar_3: scala.Option[java.lang.String] = scala.None;
  var envVar_4: scala.Option[scala.Tuple2[scala.collection.immutable.WrappedString, scala.Tuple2[scala.Int, scala.Tuple2[scala.collection.immutable.WrappedString, scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.MutVar[scala.Int], scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.MutVar[scala.Int], squid.lib.`package`.MutVar[scala.Boolean]]]]]]]]]] = scala.None;
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
            envVar_4 = scala.Some.apply[scala.Tuple2[scala.collection.immutable.WrappedString, scala.Tuple2[scala.Int, scala.Tuple2[scala.collection.immutable.WrappedString, scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.MutVar[scala.Int], scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.MutVar[scala.Int], squid.lib.`package`.MutVar[scala.Boolean]]]]]]]]]](scala.Tuple2.apply[scala.collection.immutable.WrappedString, scala.Tuple2[scala.Int, scala.Tuple2[scala.collection.immutable.WrappedString, scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.MutVar[scala.Int], scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.MutVar[scala.Int], squid.lib.`package`.MutVar[scala.Boolean]]]]]]]]](ClosureVar_12, scala.Tuple2.apply[scala.Int, scala.Tuple2[scala.collection.immutable.WrappedString, scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.MutVar[scala.Int], scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.MutVar[scala.Int], squid.lib.`package`.MutVar[scala.Boolean]]]]]]]](ClosureVar_14, scala.Tuple2.apply[scala.collection.immutable.WrappedString, scala.Tuple2[scala.Int, scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.MutVar[scala.Int], scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.MutVar[scala.Int], squid.lib.`package`.MutVar[scala.Boolean]]]]]]](ClosureVar_15, scala.Tuple2.apply[scala.Int, scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.MutVar[scala.Int], scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.MutVar[scala.Int], squid.lib.`package`.MutVar[scala.Boolean]]]]]](ClosureVar_17, scala.Tuple2.apply[scala.Int, scala.Tuple2[squid.lib.`package`.MutVar[scala.Int], scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.MutVar[scala.Int], squid.lib.`package`.MutVar[scala.Boolean]]]]](ClosureVar_18, scala.Tuple2.apply[squid.lib.`package`.MutVar[scala.Int], scala.Tuple2[scala.Int, scala.Tuple2[squid.lib.`package`.MutVar[scala.Int], squid.lib.`package`.MutVar[scala.Boolean]]]](squid.lib.MutVarProxy[scala.Int](ClosureVar_19, ((a) => ClosureVar_19 = a)), scala.Tuple2.apply[scala.Int, scala.Tuple2[squid.lib.`package`.MutVar[scala.Int], squid.lib.`package`.MutVar[scala.Boolean]]](ClosureVar_20, scala.Tuple2.apply[squid.lib.`package`.MutVar[scala.Int], squid.lib.`package`.MutVar[scala.Boolean]](squid.lib.MutVarProxy[scala.Int](ClosureVar_21, ((a) => ClosureVar_21 = a)), squid.lib.MutVarProxy[scala.Boolean](v_22, ((a) => v_22 = a)))))))))));
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
            val sch_30 = x_25.get;
            val sch_31 = sch_30._2._2;
            val sch_32 = sch_31._2._2;
            val sch_33 = sch_32._2;
            val sch_34 = sch_33._2;
            val sch_35 = sch_34._2;
            val sch_36 = sch_35._2;
            var next_37: scala.Option[scala.Char] = scala.None;
            val x_38 = sch_36.!;
            if (x_38)
              {
                val sch_39 = sch_33._1;
                val sch_40 = sch_32._1;
                while ({
                  val x_41 = sch_39.!;
                  x_41.<(sch_40).&&({
                    val x_42 = sch_39.!;
                    val x_43 = ((sch_30._1): scala.collection.IndexedSeq[scala.Char]).apply(x_42);
                    val x_44 = sch_39.!;
                    sch_39.:=(x_44.+(1));
                    next_37 = scala.Some.apply[scala.Char](x_43);
                    false
                  })
                }) 
                  ()
                ;
                val x_45 = sch_39.!;
                if (x_45.==(sch_40))
                  sch_36.:=(false)
                else
                  ()
              }
            else
              ();
            val x_46 = next_37;
            if (x_46.isDefined.`unary_!`)
              {
                val sch_47 = sch_35._1;
                val sch_48 = sch_34._1;
                while ({
                  val x_49 = sch_47.!;
                  x_49.<(sch_48).&&({
                    val x_50 = sch_47.!;
                    val x_51 = ((sch_31._1): scala.collection.IndexedSeq[scala.Char]).apply(x_50);
                    val x_52 = sch_47.!;
                    sch_47.:=(x_52.+(1));
                    next_37 = scala.Some.apply[scala.Char](x_51);
                    false
                  })
                }) 
                  ()
                ;
                val x_53 = sch_47.!;
                if (x_53.==(sch_48))
                  finished_27 = true
                else
                  ()
              }
            else
              ();
            val x_54 = next_37;
            if (x_54.isDefined)
              {
                val x_55 = dropped_5;
                val x_60 = if (x_55.<(x_1.length()))
                  {
                    val x_56 = dropped_5;
                    dropped_5 = x_56.+(1);
                    true
                  }
                else
                  {
                    val x_57 = cur_6;
                    val x_58 = scala.Predef.augmentString(x_57);
                    val x_59 = x_58.:+[scala.Char, java.lang.String](x_54.get)(scala.Predef.StringCanBuildFrom);
                    cur_6 = x_59;
                    true
                  };
                continue_8 = x_60;
                val x_61 = continue_8;
                cont_26 = x_61
              }
            else
              finished_27 = true
          }
        ;
        val x_62 = finished_27;
        if (x_62)
          envVar_4 = scala.None
        else
          ()
      };
    val x_63 = completed_7;
    x_63.`unary_!`.&&(continue_8)
  }) 
    ()
  ;
  completed_7;
  cur_6
})

// === LateImperative ===

// Transfo time: 0ms  Stringifying time: 133ms

// Same as above.

// === VarFlattening ===

// Transfo time: 375ms  Stringifying time: 123ms

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
                val x_71 = if (x_65.<(x_3.length()))
                  {
                    val x_66 = dropped_17;
                    dropped_17 = x_66.+(1);
                    true
                  }
                else
                  {
                    val x_67 = cur_18;
                    val x_68 = scala.Predef.augmentString(x_67);
                    val x_69 = optVal_45;
                    val x_70 = x_68.:+[scala.Char, java.lang.String](x_69)(scala.Predef.StringCanBuildFrom);
                    cur_18 = x_70;
                    true
                  };
                continue_20 = x_71;
                val x_72 = continue_20;
                cont_40 = x_72
              }
            else
              finished_41 = true
          }
        ;
        val x_73 = finished_41;
        if (x_73)
          isDefined_7 = false
        else
          ()
      };
    val x_74 = completed_19;
    x_74.`unary_!`.&&(continue_20)
  }) 
    ()
  ;
  completed_19;
  cur_18
})

// === Low-Level Norm ===

// Transfo time: 101ms  Stringifying time: 142ms

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
                val sch_64 = x_2.length();
                val x_65 = dropped_16;
                val sch_66 = x_65.<(sch_64);
                if (sch_66)
                  {
                    val x_67 = dropped_16;
                    dropped_16 = x_67.+(1)
                  }
                else
                  ();
                val x_72 = sch_66.`unary_!`.&&({
                  if (sch_66)
                    ()
                  else
                    {
                      val x_68 = cur_17;
                      val x_69 = scala.Predef.augmentString(x_68);
                      val x_70 = optVal_44;
                      val x_71 = x_69.:+[scala.Char, java.lang.String](x_70)(scala.Predef.StringCanBuildFrom);
                      cur_17 = x_71
                    };
                  sch_66
                });
                continue_19 = x_72.`unary_!`;
                val x_73 = continue_19;
                cont_39 = x_73
              }
            else
              finished_40 = true
          }
        ;
        val x_74 = finished_40;
        if (x_74)
          isDefined_6 = false
        else
          ()
      }
    else
      completed_18 = true;
    val x_75 = completed_18;
    x_75.`unary_!`.&&(continue_19)
  }) 
    ()
  ;
  completed_18;
  cur_17
})

// === ReNorm (should be the same) ===

// Transfo time: 78ms  Stringifying time: 83ms

// Same as above.
