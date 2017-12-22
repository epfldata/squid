// Automatically-generated code

// === Init ===

// Transfo time: 0ms  Stringifying time: 15ms

((xs_0: scala.collection.IndexedSeq[scala.Int], ys_1: scala.collection.Iterable[scala.Int]) => {
  val x_2 = xs_0.size;
  val x_3 = new sfusion.Sequence[scala.Int]((() => sfusion.impl.`package`.fromIndexed[scala.Int](xs_0)), scala.`package`.Left.apply[scala.Int, scala.Nothing](x_2));
  val x_8 = x_3.flatMap[scala.Int](((x_4: scala.Int) => {
    val x_6 = new sfusion.Sequence[scala.Int]((() => {
      val x_5 = ys_1.iterator;
      sfusion.impl.`package`.fromIterator[scala.Int](x_5)
    }), scala.`package`.Right.apply[scala.Nothing, scala.Boolean](false));
    x_6.map[scala.Int](((x$9_7: scala.Int) => x$9_7.+(x_4)))
  }));
  val x_10 = new sfusion.Sequence[scala.Int]((() => {
    val x_9 = ys_1.iterator;
    sfusion.impl.`package`.fromIterator[scala.Int](x_9)
  }), scala.`package`.Right.apply[scala.Nothing, scala.Boolean](false));
  val x_11 = x_8.zip[scala.Int](x_10);
  x_11.fold[java.lang.String]("")(((acc_12: java.lang.String, xy_13: scala.Tuple2[scala.Int, scala.Int]) => {
    val x_14 = acc_12.+(xy_13._1);
    x_14.+(xy_13._2)
  }))
})

// === HL ===

// Transfo time: 1ms  Stringifying time: 6ms

// Same as above.

// === Impl ===

// Transfo time: 7ms  Stringifying time: 38ms

((xs_0: scala.collection.IndexedSeq[scala.Int], ys_1: scala.collection.Iterable[scala.Int]) => {
  val x_2 = xs_0.size;
  val x_3 = new sfusion.Sequence[scala.Int]((() => sfusion.impl.`package`.fromIndexed[scala.Int](xs_0)), scala.`package`.Left.apply[scala.Int, scala.Nothing](x_2));
  val x_15 = new sfusion.Sequence[scala.Int]((() => {
    val x_4 = x_3.under;
    val x_5 = x_4.apply();
    sfusion.impl.`package`.flatMap[scala.Int, scala.Int](x_5)(((x_6: scala.Int) => {
      val x_8 = new sfusion.Sequence[scala.Int]((() => {
        val x_7 = ys_1.iterator;
        sfusion.impl.`package`.fromIterator[scala.Int](x_7)
      }), scala.`package`.Right.apply[scala.Nothing, scala.Boolean](false));
      val x_9 = x_8.size;
      val x_13 = new sfusion.Sequence[scala.Int]((() => {
        val x_10 = x_8.under;
        val x_11 = x_10.apply();
        sfusion.impl.`package`.map[scala.Int, scala.Int](x_11)(((x$9_12: scala.Int) => x$9_12.+(x_6)))
      }), x_9);
      val x_14 = x_13.under;
      x_14.apply()
    }))
  }), scala.`package`.Right.apply[scala.Nothing, scala.Boolean](true));
  val x_17 = new sfusion.Sequence[scala.Int]((() => {
    val x_16 = ys_1.iterator;
    sfusion.impl.`package`.fromIterator[scala.Int](x_16)
  }), scala.`package`.Right.apply[scala.Nothing, scala.Boolean](false));
  val x_18 = x_15.size;
  val x_19 = x_17.size;
  val x_24 = new sfusion.Sequence[scala.Tuple2[scala.Int, scala.Int]]((() => {
    val x_20 = x_15.under;
    val x_21 = x_20.apply();
    val x_22 = x_17.under;
    val x_23 = x_22.apply();
    sfusion.impl.`package`.zip[scala.Int, scala.Int](x_21, x_23)
  }), sfusion.`package`.minSize(x_18, x_19));
  val x_25 = x_24.under;
  val x_26 = x_25.apply();
  sfusion.impl.`package`.fold[scala.Tuple2[scala.Int, scala.Int], java.lang.String](x_26)("")(((acc_27: java.lang.String, xy_28: scala.Tuple2[scala.Int, scala.Int]) => {
    val x_29 = acc_27.+(xy_28._1);
    x_29.+(xy_28._2)
  }))
})

// === CtorInline ===

// Transfo time: 9ms  Stringifying time: 12ms

((xs_0: scala.collection.IndexedSeq[scala.Int], ys_1: scala.collection.Iterable[scala.Int]) => {
  val x_2 = xs_0.size;
  val x_3 = sfusion.impl.`package`.fromIndexed[scala.Int](xs_0);
  val x_8 = sfusion.impl.`package`.flatMap[scala.Int, scala.Int](x_3)(((x_4: scala.Int) => {
    val x_5 = ys_1.iterator;
    val x_6 = sfusion.impl.`package`.fromIterator[scala.Int](x_5);
    sfusion.impl.`package`.map[scala.Int, scala.Int](x_6)(((x$9_7: scala.Int) => x$9_7.+(x_4)))
  }));
  val x_9 = ys_1.iterator;
  val x_10 = sfusion.impl.`package`.fromIterator[scala.Int](x_9);
  val x_11 = sfusion.impl.`package`.zip[scala.Int, scala.Int](x_8, x_10);
  sfusion.impl.`package`.fold[scala.Tuple2[scala.Int, scala.Int], java.lang.String](x_11)("")(((acc_12: java.lang.String, xy_13: scala.Tuple2[scala.Int, scala.Int]) => {
    val x_14 = acc_12.+(xy_13._1);
    x_14.+(xy_13._2)
  }))
})

// === ImplOptim ===

// Transfo time: 0ms  Stringifying time: 4ms

// Same as above.

// === Imperative ===

// Transfo time: 22ms  Stringifying time: 27ms

((xs_0: scala.collection.IndexedSeq[scala.Int], ys_1: scala.collection.Iterable[scala.Int]) => {
  val x_2 = xs_0.size;
  val x_3 = xs_0.length;
  var i_4: scala.Int = 0;
  val x_17 = sfusion.impl.`package`.flatMap[scala.Int, scala.Int](((k_5: scala.Function1[scala.Int, scala.Boolean]) => {
    while ({
      val x_6 = i_4;
      x_6.<(x_3).&&({
        val x_7 = i_4;
        val x_8 = xs_0.apply(x_7);
        val x_9 = i_4;
        i_4 = x_9.+(1);
        k_5(x_8)
      })
    }) 
      ()
    ;
    val x_10 = i_4;
    x_10.==(x_3)
  }))(((x_11: scala.Int) => {
    val x_12 = ys_1.iterator;
    ((k_13: scala.Function1[scala.Int, scala.Boolean]) => {
      while ({
        val x_14 = x_12.hasNext;
        x_14.&&({
          val x_15 = x_12.next();
          k_13(x_15.+(x_11))
        })
      }) 
        ()
      ;
      val x_16 = x_12.hasNext;
      x_16.`unary_!`
    })
  }));
  val x_18 = ys_1.iterator;
  var cur_19: java.lang.String = "";
  var b_finished_20: scala.Boolean = false;
  val x_29 = x_17(((a_21: scala.Int) => {
    var cont_22: scala.Boolean = true;
    while ({
      val x_23 = x_18.hasNext;
      x_23.&&({
        val x_24 = x_18.next();
        val x_25 = cur_19;
        cur_19 = x_25.+(a_21).+(x_24);
        cont_22 = true;
        false
      })
    }) 
      ()
    ;
    val x_26 = x_18.hasNext;
    b_finished_20 = x_26.`unary_!`;
    val x_27 = cont_22;
    x_27.&&({
      val x_28 = b_finished_20;
      x_28.`unary_!`
    })
  }));
  x_29.||(b_finished_20);
  cur_19
})

// === FlatMapFusion ===

// Transfo time: 12ms  Stringifying time: 40ms

((xs_0: scala.collection.IndexedSeq[scala.Int], ys_1: scala.collection.Iterable[scala.Int]) => {
  val x_2 = xs_0.size;
  val x_3 = xs_0.length;
  var i_4: scala.Int = 0;
  var aVar_5: scala.Option[scala.Int] = scala.None;
  var envVar_6: scala.Option[scala.collection.Iterator[scala.Int]] = scala.None;
  val x_7 = ys_1.iterator;
  var cur_8: java.lang.String = "";
  var b_finished_9: scala.Boolean = false;
  var completed_10: scala.Boolean = false;
  var continue_11: scala.Boolean = false;
  while ({
    val x_12 = envVar_6;
    if (x_12.isDefined.`unary_!`)
      {
        while ({
          val x_13 = i_4;
          x_13.<(x_3).&&({
            val x_14 = i_4;
            val x_15 = xs_0.apply(x_14);
            val x_16 = i_4;
            i_4 = x_16.+(1);
            aVar_5 = scala.Some.apply[scala.Int](x_15);
            val x_17 = ys_1.iterator;
            envVar_6 = scala.Some.apply[scala.collection.Iterator[scala.Int]](x_17);
            false
          })
        }) 
          ()
        ;
        val x_18 = i_4;
        x_18.==(x_3)
      }
    else
      ();
    val x_19 = envVar_6;
    if (x_19.isDefined.`unary_!`)
      completed_10 = true
    else
      {
        val x_20 = envVar_6;
        while ({
          val x_21 = x_20.get.hasNext;
          x_21.&&({
            val x_22 = x_20.get.next();
            val x_23 = aVar_5;
            var cont_24: scala.Boolean = true;
            while ({
              val x_25 = x_7.hasNext;
              x_25.&&({
                val x_26 = x_7.next();
                val x_27 = cur_8;
                cur_8 = x_27.+(x_22.+(x_23.get)).+(x_26);
                cont_24 = true;
                false
              })
            }) 
              ()
            ;
            val x_28 = x_7.hasNext;
            b_finished_9 = x_28.`unary_!`;
            val x_29 = cont_24;
            val x_31 = x_29.&&({
              val x_30 = b_finished_9;
              x_30.`unary_!`
            });
            continue_11 = x_31;
            continue_11
          })
        }) 
          ()
        ;
        val x_32 = x_20.get.hasNext;
        if (x_32.`unary_!`)
          envVar_6 = scala.None
        else
          ()
      };
    val x_33 = completed_10;
    x_33.`unary_!`.&&(continue_11)
  }) 
    ()
  ;
  val x_34 = completed_10;
  x_34.||(b_finished_9);
  cur_8
})

// === LateImperative ===

// Transfo time: 0ms  Stringifying time: 35ms

// Same as above.

// === VarFlattening ===

// Transfo time: 22ms  Stringifying time: 41ms

((xs_0: scala.collection.IndexedSeq[scala.Int], ys_1: scala.collection.Iterable[scala.Int]) => {
  val x_2 = xs_0.size;
  val x_3 = xs_0.length;
  var i_4: scala.Int = 0;
  var isDefined_5: scala.Boolean = false;
  var optVal_6: scala.Int = squid.lib.`package`.uncheckedNullValue[scala.Int];
  var isDefined_7: scala.Boolean = false;
  var optVal_8: scala.collection.Iterator[scala.Int] = squid.lib.`package`.uncheckedNullValue[scala.collection.Iterator[scala.Int]];
  val x_9 = ys_1.iterator;
  var cur_10: java.lang.String = "";
  var b_finished_11: scala.Boolean = false;
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
            val x_19 = ys_1.iterator;
            optVal_8 = x_19;
            isDefined_7 = true;
            false
          })
        }) 
          ()
        ;
        val x_20 = i_4;
        x_20.==(x_3)
      }
    else
      ();
    val x_21 = isDefined_7;
    if (x_21.`unary_!`)
      completed_12 = true
    else
      {
        while ({
          val x_22 = optVal_8;
          val x_23 = x_22.hasNext;
          x_23.&&({
            val x_24 = optVal_8;
            val x_25 = x_24.next();
            var cont_26: scala.Boolean = true;
            while ({
              val x_27 = x_9.hasNext;
              x_27.&&({
                val x_28 = x_9.next();
                val x_29 = cur_10;
                val x_30 = optVal_6;
                cur_10 = x_29.+(x_25.+(x_30)).+(x_28);
                cont_26 = true;
                false
              })
            }) 
              ()
            ;
            val x_31 = x_9.hasNext;
            b_finished_11 = x_31.`unary_!`;
            val x_32 = cont_26;
            val x_34 = x_32.&&({
              val x_33 = b_finished_11;
              x_33.`unary_!`
            });
            continue_13 = x_34;
            continue_13
          })
        }) 
          ()
        ;
        val x_35 = optVal_8;
        val x_36 = x_35.hasNext;
        if (x_36.`unary_!`)
          isDefined_7 = false
        else
          ()
      };
    val x_37 = completed_12;
    x_37.`unary_!`.&&(continue_13)
  }) 
    ()
  ;
  val x_38 = completed_12;
  x_38.||(b_finished_11);
  cur_10
})

// === Low-Level Norm ===

// Transfo time: 21ms  Stringifying time: 45ms

((xs_0: scala.collection.IndexedSeq[scala.Int], ys_1: scala.collection.Iterable[scala.Int]) => {
  val x_2 = xs_0.size;
  val x_3 = xs_0.length;
  var i_4: scala.Int = 0;
  var isDefined_5: scala.Boolean = false;
  var optVal_6: scala.Int = 0;
  var isDefined_7: scala.Boolean = false;
  var optVal_8: scala.collection.Iterator[scala.Int] = null;
  val x_9 = ys_1.iterator;
  var cur_10: java.lang.String = "";
  var b_finished_11: scala.Boolean = false;
  var completed_12: scala.Boolean = false;
  var continue_13: scala.Boolean = false;
  while ({
    val x_14 = isDefined_7;
    if (x_14)
      ()
    else
      {
        val x_15 = i_4;
        if (x_15.<(x_3))
          {
            val x_16 = i_4;
            val x_17 = xs_0.apply(x_16);
            val x_18 = i_4;
            i_4 = x_18.+(1);
            optVal_6 = x_17;
            isDefined_5 = true;
            val x_19 = ys_1.iterator;
            optVal_8 = x_19;
            isDefined_7 = true
          }
        else
          ();
        val x_20 = i_4;
        x_20.==(x_3)
      };
    val x_21 = isDefined_7;
    if (x_21)
      {
        while ({
          val x_22 = optVal_8;
          val x_23 = x_22.hasNext;
          x_23.&&({
            val x_24 = optVal_8;
            val x_25 = x_24.next();
            var cont_26: scala.Boolean = true;
            val x_27 = x_9.hasNext;
            if (x_27)
              {
                val x_28 = x_9.next();
                val x_29 = cur_10;
                val x_30 = optVal_6;
                cur_10 = x_29.+(x_25.+(x_30)).+(x_28);
                cont_26 = true
              }
            else
              ();
            val x_31 = x_9.hasNext;
            b_finished_11 = x_31.`unary_!`;
            val x_32 = cont_26;
            val x_34 = x_32.&&({
              val x_33 = b_finished_11;
              x_33.`unary_!`
            });
            continue_13 = x_34;
            continue_13
          })
        }) 
          ()
        ;
        val x_35 = optVal_8;
        val x_36 = x_35.hasNext;
        if (x_36)
          ()
        else
          isDefined_7 = false
      }
    else
      completed_12 = true;
    val x_37 = completed_12;
    x_37.`unary_!`.&&(continue_13)
  }) 
    ()
  ;
  val x_38 = completed_12;
  val x_40 = x_38.`unary_!`.&&({
    val x_39 = b_finished_11;
    x_39.`unary_!`
  });
  cur_10
})

// === ReNorm (should be the same) ===

// Transfo time: 9ms  Stringifying time: 28ms

// Same as above.
