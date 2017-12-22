// Automatically-generated code

// === Init ===

// Transfo time: 0ms  Stringifying time: 20ms

{
  val posNats_1 = new sfusion.Sequence[scala.Int]((() => sfusion.impl.`package`.iterate[scala.Int](1)(((x$1_0: scala.Int) => x$1_0.+(1)))), scala.`package`.Right.apply[scala.Nothing, scala.Boolean](false));
  val odds_3 = posNats_1.map[scala.Int](((x$2_2: scala.Int) => x$2_2.*(2).+(1)));
  val divs_4 = odds_3.+:[scala.Int](2);
  val x_12 = posNats_1.filter(((n_5: scala.Int) => {
    val x_6 = scala.math.`package`.sqrt(n_5.toDouble);
    val x_7 = scala.Predef.doubleWrapper(x_6);
    val x_8 = x_7.ceil;
    val x_10 = divs_4.takeWhile(((x$4_9: scala.Int) => x$4_9.<=(x_8.toInt)));
    x_10.forall(((d_11: scala.Int) => n_5.%(d_11).!=(0)))
  }));
  val x_13 = x_12.+:[scala.Int](2);
  val x_14 = x_13.take(100);
  x_14.fold[scala.Int](0)(((x$6_15: scala.Int, x$7_16: scala.Int) => x$6_15.+(x$7_16)))
}

// === HL ===

// Transfo time: 8ms  Stringifying time: 12ms

// Same as above.

// === Impl ===

// Transfo time: 44ms  Stringifying time: 68ms

{
  val posNats_1 = new sfusion.Sequence[scala.Int]((() => sfusion.impl.`package`.iterate[scala.Int](1)(((x$1_0: scala.Int) => x$1_0.+(1)))), scala.`package`.Right.apply[scala.Nothing, scala.Boolean](false));
  val x_2 = posNats_1.size;
  val x_6 = new sfusion.Sequence[scala.Int]((() => {
    val x_3 = posNats_1.under;
    val x_4 = x_3.apply();
    sfusion.impl.`package`.map[scala.Int, scala.Int](x_4)(((x$2_5: scala.Int) => x$2_5.*(2).+(1)))
  }), x_2);
  val x_7 = x_6.size;
  val x_11 = new sfusion.Sequence[scala.Int]((() => {
    val x_8 = sfusion.impl.`package`.single[scala.Int](2);
    val x_9 = x_6.under;
    val x_10 = x_9.apply();
    sfusion.impl.`package`.concat[scala.Int](x_8, x_10)
  }), sfusion.`package`.addToSize(x_7, 1));
  val x_12 = posNats_1.size;
  val x_27 = new sfusion.Sequence[scala.Int]((() => {
    val x_13 = posNats_1.under;
    val x_14 = x_13.apply();
    sfusion.impl.`package`.filter[scala.Int](x_14)(((n_15: scala.Int) => {
      val x_16 = scala.math.`package`.sqrt(n_15.toDouble);
      val x_17 = scala.Predef.doubleWrapper(x_16);
      val x_18 = x_17.ceil;
      val x_19 = x_11.size;
      val x_23 = new sfusion.Sequence[scala.Int]((() => {
        val x_20 = x_11.under;
        val x_21 = x_20.apply();
        sfusion.impl.`package`.takeWhile[scala.Int](x_21)(((x$4_22: scala.Int) => x$4_22.<=(x_18.toInt)))
      }), x_19);
      val x_24 = x_23.under;
      val x_25 = x_24.apply();
      sfusion.impl.`package`.all[scala.Int](x_25)(((d_26: scala.Int) => n_15.%(d_26).!=(0)))
    }))
  }), x_12);
  val x_28 = x_27.size;
  val x_32 = new sfusion.Sequence[scala.Int]((() => {
    val x_29 = sfusion.impl.`package`.single[scala.Int](2);
    val x_30 = x_27.under;
    val x_31 = x_30.apply();
    sfusion.impl.`package`.concat[scala.Int](x_29, x_31)
  }), sfusion.`package`.addToSize(x_28, 1));
  val x_33 = x_32.size;
  val x_36 = new sfusion.Sequence[scala.Int]((() => {
    val x_34 = x_32.under;
    val x_35 = x_34.apply();
    sfusion.impl.`package`.take[scala.Int](x_35)(100)
  }), sfusion.`package`.minSize(x_33, scala.`package`.Left.apply[scala.Int, scala.Nothing](100)));
  val x_37 = x_36.under;
  val x_38 = x_37.apply();
  sfusion.impl.`package`.fold[scala.Int, scala.Int](x_38)(0)(((x$6_39: scala.Int, x$7_40: scala.Int) => x$6_39.+(x$7_40)))
}

// === CtorInline ===

// Transfo time: 60ms  Stringifying time: 30ms

{
  val x_0 = sfusion.impl.`package`.single[scala.Int](2);
  val x_2 = sfusion.impl.`package`.iterate[scala.Int](1)(((x$1$70_1: scala.Int) => x$1$70_1.+(1)));
  val x_16 = sfusion.impl.`package`.filter[scala.Int](x_2)(((n_3: scala.Int) => {
    val x_4 = scala.math.`package`.sqrt(n_3.toDouble);
    val x_5 = scala.Predef.doubleWrapper(x_4);
    val x_6 = x_5.ceil;
    val x_7 = sfusion.impl.`package`.single[scala.Int](2);
    val x_9 = sfusion.impl.`package`.iterate[scala.Int](1)(((x$1_8: scala.Int) => x$1_8.+(1)));
    val x_11 = sfusion.impl.`package`.map[scala.Int, scala.Int](x_9)(((x$2_10: scala.Int) => x$2_10.*(2).+(1)));
    val x_12 = sfusion.impl.`package`.concat[scala.Int](x_7, x_11);
    val x_14 = sfusion.impl.`package`.takeWhile[scala.Int](x_12)(((x$4_13: scala.Int) => x$4_13.<=(x_6.toInt)));
    sfusion.impl.`package`.all[scala.Int](x_14)(((d_15: scala.Int) => n_3.%(d_15).!=(0)))
  }));
  val x_17 = sfusion.impl.`package`.concat[scala.Int](x_0, x_16);
  val x_18 = sfusion.impl.`package`.take[scala.Int](x_17)(100);
  sfusion.impl.`package`.fold[scala.Int, scala.Int](x_18)(0)(((x$6_19: scala.Int, x$7_20: scala.Int) => x$6_19.+(x$7_20)))
}

// === ImplOptim ===

// Transfo time: 0ms  Stringifying time: 16ms

// Same as above.

// === Imperative ===

// Transfo time: 143ms  Stringifying time: 74ms

{
  var cur_0: scala.Int = 1;
  var curIsLhs_1: scala.Boolean = true;
  var taken_2: scala.Int = 0;
  var cur_3: scala.Int = 0;
  var cont_4: scala.Boolean = true;
  var finished_5: scala.Boolean = false;
  while ({
    val x_6 = cont_4;
    x_6.&&({
      val x_7 = finished_5;
      x_7.`unary_!`
    })
  }) 
    {
      var next_8: scala.Option[scala.Int] = scala.None;
      val x_9 = curIsLhs_1;
      if (x_9)
        {
          next_8 = scala.Some.apply[scala.Int](2);
          if (true)
            curIsLhs_1 = false
          else
            ()
        }
      else
        ();
      val x_10 = next_8;
      if (x_10.isDefined.`unary_!`)
        {
          while ({
            val x_11 = cur_0;
            val x_12 = scala.math.`package`.sqrt(x_11.toDouble);
            val x_13 = scala.Predef.doubleWrapper(x_12);
            val x_14 = x_13.ceil;
            var cur_15: scala.Int = 1;
            var curIsLhs_16: scala.Boolean = true;
            var stop_17: scala.Boolean = false;
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
                var next_22: scala.Option[scala.Int] = scala.None;
                val x_23 = curIsLhs_16;
                if (x_23)
                  {
                    next_22 = scala.Some.apply[scala.Int](2);
                    if (true)
                      curIsLhs_16 = false
                    else
                      ()
                  }
                else
                  ();
                val x_24 = next_22;
                if (x_24.isDefined.`unary_!`)
                  {
                    while ({
                      val x_25 = cur_15;
                      next_22 = scala.Some.apply[scala.Int](x_25.*(2).+(1));
                      false.&&({
                        val x_26 = cur_15;
                        cur_15 = x_26.+(1);
                        true
                      })
                    }) 
                      ()
                    ;
                    if (false)
                      finished_19 = true
                    else
                      ()
                  }
                else
                  ();
                val x_27 = next_22;
                if (x_27.isDefined)
                  {
                    val x_28 = if (x_27.get.<=(x_14.toInt))
                      x_11.%(x_27.get).!=(0)
                    else
                      {
                        stop_17 = true;
                        false
                      };
                    cont_18 = x_28
                  }
                else
                  finished_19 = true
              }
            ;
            val x_29 = finished_19;
            val x_30 = x_29.||(stop_17);
            val x_31 = x_30.`unary_!`.||({
              next_8 = scala.Some.apply[scala.Int](x_11);
              false
            });
            x_31.&&({
              val x_32 = cur_0;
              cur_0 = x_32.+(1);
              true
            })
          }) 
            ()
          ;
          if (false)
            finished_5 = true
          else
            ()
        }
      else
        ();
      val x_33 = next_8;
      if (x_33.isDefined)
        {
          val x_34 = taken_2;
          val x_38 = x_34.<(100).&&({
            val x_35 = taken_2;
            taken_2 = x_35.+(1);
            val x_36 = cur_3;
            cur_3 = x_36.+(x_33.get);
            true.&&({
              val x_37 = taken_2;
              x_37.<(100)
            })
          });
          cont_4 = x_38
        }
      else
        finished_5 = true
    }
  ;
  val x_39 = finished_5;
  x_39.||({
    val x_40 = taken_2;
    x_40.==(100)
  });
  cur_3
}

// === FlatMapFusion ===

// Transfo time: 1ms  Stringifying time: 97ms

// Same as above.

// === LateImperative ===

// Transfo time: 0ms  Stringifying time: 83ms

// Same as above.

// === VarFlattening ===

// Transfo time: 67ms  Stringifying time: 93ms

{
  var cur_0: scala.Int = 1;
  var curIsLhs_1: scala.Boolean = true;
  var taken_2: scala.Int = 0;
  var cur_3: scala.Int = 0;
  var cont_4: scala.Boolean = true;
  var finished_5: scala.Boolean = false;
  while ({
    val x_6 = cont_4;
    x_6.&&({
      val x_7 = finished_5;
      x_7.`unary_!`
    })
  }) 
    {
      var isDefined_8: scala.Boolean = false;
      var optVal_9: scala.Int = squid.lib.`package`.uncheckedNullValue[scala.Int];
      val x_10 = curIsLhs_1;
      if (x_10)
        {
          optVal_9 = 2;
          isDefined_8 = true;
          if (true)
            curIsLhs_1 = false
          else
            ()
        }
      else
        ();
      val x_11 = isDefined_8;
      if (x_11.`unary_!`)
        {
          while ({
            val x_12 = cur_0;
            val x_13 = scala.math.`package`.sqrt(x_12.toDouble);
            val x_14 = scala.Predef.doubleWrapper(x_13);
            val x_15 = x_14.ceil;
            var cur_16: scala.Int = 1;
            var curIsLhs_17: scala.Boolean = true;
            var stop_18: scala.Boolean = false;
            var cont_19: scala.Boolean = true;
            var finished_20: scala.Boolean = false;
            while ({
              val x_21 = cont_19;
              x_21.&&({
                val x_22 = finished_20;
                x_22.`unary_!`
              })
            }) 
              {
                var isDefined_23: scala.Boolean = false;
                var optVal_24: scala.Int = squid.lib.`package`.uncheckedNullValue[scala.Int];
                val x_25 = curIsLhs_17;
                if (x_25)
                  {
                    optVal_24 = 2;
                    isDefined_23 = true;
                    if (true)
                      curIsLhs_17 = false
                    else
                      ()
                  }
                else
                  ();
                val x_26 = isDefined_23;
                if (x_26.`unary_!`)
                  {
                    while ({
                      val x_27 = cur_16;
                      optVal_24 = x_27.*(2).+(1);
                      isDefined_23 = true;
                      false.&&({
                        val x_28 = cur_16;
                        cur_16 = x_28.+(1);
                        true
                      })
                    }) 
                      ()
                    ;
                    if (false)
                      finished_20 = true
                    else
                      ()
                  }
                else
                  ();
                val x_29 = isDefined_23;
                if (x_29)
                  {
                    val x_30 = optVal_24;
                    val x_32 = if (x_30.<=(x_15.toInt))
                      {
                        val x_31 = optVal_24;
                        x_12.%(x_31).!=(0)
                      }
                    else
                      {
                        stop_18 = true;
                        false
                      };
                    cont_19 = x_32
                  }
                else
                  finished_20 = true
              }
            ;
            val x_33 = finished_20;
            val x_34 = x_33.||(stop_18);
            val x_35 = x_34.`unary_!`.||({
              optVal_9 = x_12;
              isDefined_8 = true;
              false
            });
            x_35.&&({
              val x_36 = cur_0;
              cur_0 = x_36.+(1);
              true
            })
          }) 
            ()
          ;
          if (false)
            finished_5 = true
          else
            ()
        }
      else
        ();
      val x_37 = isDefined_8;
      if (x_37)
        {
          val x_38 = taken_2;
          val x_43 = x_38.<(100).&&({
            val x_39 = taken_2;
            taken_2 = x_39.+(1);
            val x_40 = cur_3;
            val x_41 = optVal_9;
            cur_3 = x_40.+(x_41);
            true.&&({
              val x_42 = taken_2;
              x_42.<(100)
            })
          });
          cont_4 = x_43
        }
      else
        finished_5 = true
    }
  ;
  val x_44 = finished_5;
  x_44.||({
    val x_45 = taken_2;
    x_45.==(100)
  });
  cur_3
}

// === Low-Level Norm ===

// Transfo time: 240ms  Stringifying time: 100ms

{
  var cur_0: scala.Int = 1;
  var curIsLhs_1: scala.Boolean = true;
  var taken_2: scala.Int = 0;
  var cur_3: scala.Int = 0;
  var cont_4: scala.Boolean = true;
  var finished_5: scala.Boolean = false;
  while ({
    val x_6 = cont_4;
    x_6.&&({
      val x_7 = finished_5;
      x_7.`unary_!`
    })
  }) 
    {
      var isDefined_8: scala.Boolean = false;
      var optVal_9: scala.Int = 0;
      val x_10 = curIsLhs_1;
      if (x_10)
        {
          optVal_9 = 2;
          isDefined_8 = true;
          curIsLhs_1 = false
        }
      else
        ();
      val x_11 = isDefined_8;
      if (x_11)
        ()
      else
        while ({
          val x_12 = cur_0;
          val x_13 = scala.math.`package`.sqrt(x_12.toDouble);
          val x_14 = scala.Predef.doubleWrapper(x_13);
          val x_15 = x_14.ceil;
          var cur_16: scala.Int = 1;
          var curIsLhs_17: scala.Boolean = true;
          var stop_18: scala.Boolean = false;
          var cont_19: scala.Boolean = true;
          var finished_20: scala.Boolean = false;
          while ({
            val x_21 = cont_19;
            x_21.&&({
              val x_22 = finished_20;
              x_22.`unary_!`
            })
          }) 
            {
              var isDefined_23: scala.Boolean = false;
              var optVal_24: scala.Int = 0;
              val x_25 = curIsLhs_17;
              if (x_25)
                {
                  optVal_24 = 2;
                  isDefined_23 = true;
                  curIsLhs_17 = false
                }
              else
                ();
              val x_26 = isDefined_23;
              if (x_26)
                ()
              else
                {
                  val x_27 = cur_16;
                  optVal_24 = x_27.*(2).+(1);
                  isDefined_23 = true
                };
              val x_28 = isDefined_23;
              if (x_28)
                {
                  val x_29 = optVal_24;
                  val x_31 = x_29.<=(x_15.toInt).&&({
                    val x_30 = optVal_24;
                    x_12.%(x_30).!=(0)
                  });
                  if (x_31)
                    ()
                  else
                    if (x_29.<=(x_15.toInt))
                      ()
                    else
                      stop_18 = true;
                  cont_19 = x_31
                }
              else
                finished_20 = true
            }
          ;
          val x_32 = finished_20;
          val x_34 = x_32.`unary_!`.&&({
            val x_33 = stop_18;
            x_33.`unary_!`
          });
          if (x_34)
            ()
          else
            {
              optVal_9 = x_12;
              isDefined_8 = true
            };
          if (x_34)
            {
              val x_35 = cur_0;
              cur_0 = x_35.+(1)
            }
          else
            ();
          x_34
        }) 
          ()
        ;
      val x_36 = isDefined_8;
      if (x_36)
        {
          val x_37 = taken_2;
          val x_42 = x_37.<(100).&&({
            val x_38 = taken_2;
            taken_2 = x_38.+(1);
            val x_39 = cur_3;
            val x_40 = optVal_9;
            cur_3 = x_39.+(x_40);
            val x_41 = taken_2;
            x_41.<(100)
          });
          cont_4 = x_42
        }
      else
        finished_5 = true
    }
  ;
  val x_43 = finished_5;
  val x_45 = x_43.`unary_!`.&&({
    val x_44 = taken_2;
    x_44.==(100).`unary_!`
  });
  cur_3
}

// === ReNorm (should be the same) ===

// Transfo time: 35ms  Stringifying time: 90ms

// Same as above.
