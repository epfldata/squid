package squid
package functional

import squid.utils.meta.RuntimeUniverseHelpers.sru

class MultiStage extends MyFunSuite {
  import TestDSL.Predef._
  import TestDSL.Quasicodes._
  
  // FIXME class loading
  //test("Nested Quoted Types") {
  //  
  //  val reprep = ir"MultiStage.rep" : Q[ Q[Double, {}], {} ]
  //  val rep = reprep.run
  //  
  //  assert(rep == MultiStage.rep)
  //  
  //}
  
  test("Nested ir expressions") {
    
    {
      val ir2 = ir{ ir{42} } : Code[Code[Int,{}],{}]
      val ir1 = ir2.run : Code[Int,{}]
      assert(ir1 =~= code"42")
      assert(ir1.run == 42)
    }
    
    {
      val ir2 = ir{ ir{scala.None} } : Code[Code[Option[Int],{}],{}]
      val ir1 = ir2.run : Code[Option[Int],{}]
      assert(ir1 =~= code"scala.None")
      assert(ir1.run == scala.None)
    }
    
    {
      val ir2 = ir{ ir{ List(1,2,3) map (_ + 1 toDouble) } } : Code[Code[List[Double],{}],{}]
      val ir1 = ir2.run : Code[List[Double],{}]
      assert(ir1 =~= code"List(1,2,3) map (_ + 1 toDouble)")
      assert(ir1.run == { List(1,2,3) map (_ + 1 toDouble) })
    }
    
    /* NOTE: in commit e1370f61f4072fe6a69bbff3890dc78152c56c10, a bug made that we did not try to dealias types and so
     * no type tag could be found for `base.MtdSymbol`.
     * Curiously, if we fell back on `unknownTypefallBack` even though no TypeTag was found,
     * the generated __b__.uninterpretedType[__b__.MtdSymbol], which was looking for a TypeTag[MtdSymbol],
     * made the compiler loop indefinitely -- but only when in the middle of the big gen'd code (not in isolation)!
     * (See cod eat end of file.)
     */
    
    assert(codeTypeOf[base.MtdSymbol].rep == base.uninterpretedType[sru.MethodSymbol])
    
    // Note:
    //ir{ ir{ ir{ List(1,2,3) map (_ + 1 toDouble) } } }  // Error:(49, 7) Embedding Error: Unsupported feature: TypeTag construction (for scp.utils.meta.RuntimeUniverseHelpers.sru.TypeSymbol)
    
  }
  
  test("Doubly-Nested ir expressions") {
    
    {
      val ir3 = ir{ ir{ ir{scala.None} } } : Code[Code[Code[Option[Int],{}],{}],{}]
      val ir2 = ir3.run : Code[Code[Option[Int],{}],{}]
      val ir1 = ir2.run : Code[Option[Int],{}]
      //assert(ir2 =~= ir""" ir"scala.None" """)
      // ^ Note: this one is false because ir2, which uses QC, refers to `TestDSL2.Quasicodes.qcbase` while the other,
      // which uses QQ, refers to `TestDSL2.Predef.base`, which are semantically equivalent but different trees.
      assert(ir2 =~= code""" ir{scala.None} """)
      assert(ir1 =~= code"scala.None")
      assert(ir1.run == scala.None)
    }
    
    // Note:
    // ir{ ir{ ir{ ir{scala.None} } } }  // Error:(55, 17) Embedding Error: Unsupported feature: TypeTag construction (for scp.utils.meta.RuntimeUniverseHelpers.sru.TypeSymbol)
    
  }
  
}
object MultiStage {
  import TestDSL.Predef._
  
  val rep = code"42.toDouble"
  
}


// This old gen'd code made the compiler loop, at least in e1370f61f4072fe6a69bbff3890dc78152c56c10
/*println({
  val __b__ = TestDSL2.Quasicodes.qcbase;
  TestDSL2.Quasicodes.qcbase.`internal IR`[scp.TestDSL2.IR[List[Int],Any], Any](__b__.wrapConstruct({
    val _0_TestDSL2 = __b__.staticModuleType("scp.TestDSL2");
    val _1_TestDSL2 = __b__.moduleObject("scp.TestDSL2", false);
    val _2_QuasiBase_Quasicodes_Sym = __b__.loadTypSymbol("scp.quasi2.QuasiBase$Quasicodes$");
    val _3_QuasiBase_Quasicodes_ = __b__.typeApp(_1_TestDSL2, _2_QuasiBase_Quasicodes_Sym, scala.Nil);
    val _4_qcbase = __b__.loadMtdSymbol(_2_QuasiBase_Quasicodes_Sym, "qcbase", scala.Some(0), false);
    val _5_QuasiBase_IRSym = __b__.loadTypSymbol("scp.quasi2.QuasiBase$IR");
    val _6_ListSym = __b__.loadTypSymbol("scala.collection.immutable.List");
    val _7_immutable = __b__.moduleObject("scala.collection.immutable", true);
    val _8_intSym = __b__.loadTypSymbol("int");
    val _9_scala = __b__.moduleObject("scala", true);
    val _10_int = __b__.typeApp(_9_scala, _8_intSym, scala.Nil);
    val _11_List = __b__.typeApp(_7_immutable, _6_ListSym, scala.List(_10_int));
    val _12_ObjectSym = __b__.loadTypSymbol("java.lang.Object");
    val _13_Object = __b__.typeApp(_9_scala, _12_ObjectSym, scala.Nil);
    val _14_QuasiBase_IR = __b__.typeApp(_1_TestDSL2, _5_QuasiBase_IRSym, scala.List(_11_List, _13_Object));
    val _15_SimpleAST_RepSym = __b__.loadTypSymbol("scp.ir2.SimpleAST$Rep");
    val _16_SimpleAST_Rep = __b__.typeApp(_1_TestDSL2, _15_SimpleAST_RepSym, scala.Nil);
    val _17_TestDSL2_Sym = __b__.loadTypSymbol("scp.TestDSL2$");
    val _18_loadTypSymbol = __b__.loadMtdSymbol(_17_TestDSL2_Sym, "loadTypSymbol", scala.Some(0), false);
    val _19_moduleObject = __b__.loadMtdSymbol(_17_TestDSL2_Sym, "moduleObject", scala.Some(0), false);
    val _20_ScalaTyping_TypeRepSym = __b__.loadTypSymbol("scp.ir2.ScalaTyping$TypeRep");
    val _21_ScalaTyping_TypeRep = __b__.typeApp(_1_TestDSL2, _20_ScalaTyping_TypeRepSym, scala.Nil);
    val _22_Nil = __b__.moduleObject("scala.collection.immutable.Nil", false);
    val _23_typeApp = __b__.loadMtdSymbol(_17_TestDSL2_Sym, "typeApp", scala.Some(0), false);
    val _24_List = __b__.typeApp(_7_immutable, _6_ListSym, scala.List(_21_ScalaTyping_TypeRep));
    val _25_List = __b__.moduleObject("scala.collection.immutable.List", false);
    val _26_List_Sym = __b__.loadTypSymbol("scala.collection.immutable.List$");
    val _27_apply = __b__.loadMtdSymbol(_26_List_Sym, "apply", scala.Some(0), false);
    val _28_SomeSym = __b__.loadTypSymbol("scala.Some");
    val _29_Some = __b__.typeApp(_9_scala, _28_SomeSym, scala.List(_10_int));
    val _30_Some = __b__.moduleObject("scala.Some", false);
    val _31_Some_Sym = __b__.loadTypSymbol("scala.Some$");
    val _32_apply = __b__.loadMtdSymbol(_31_Some_Sym, "apply", scala.Some(0), false);
    val _33_loadMtdSymbol = __b__.loadMtdSymbol(_17_TestDSL2_Sym, "loadMtdSymbol", scala.Some(0), false);
    val _34_Base_ArgsVarargsSym = __b__.loadTypSymbol("scp.lang2.Base$ArgsVarargs");
    val _35_Base_ArgsVarargs = __b__.typeApp(_1_TestDSL2, _34_Base_ArgsVarargsSym, scala.Nil);
    val _36_Base_ArgsVarargs_Sym = __b__.loadTypSymbol("scp.lang2.Base$ArgsVarargs$");
    val _37_Base_ArgsVarargs_ = __b__.typeApp(_1_TestDSL2, _36_Base_ArgsVarargs_Sym, scala.Nil);
    val _38_Base_ArgsSym = __b__.loadTypSymbol("scp.lang2.Base$Args");
    val _39_Base_Args = __b__.typeApp(_1_TestDSL2, _38_Base_ArgsSym, scala.Nil);
    val _40_Base_Args_Sym = __b__.loadTypSymbol("scp.lang2.Base$Args$");
    val _41_Base_Args_ = __b__.typeApp(_1_TestDSL2, _40_Base_Args_Sym, scala.Nil);
    val _42_apply = __b__.loadMtdSymbol(_40_Base_Args_Sym, "apply", scala.Some(0), false);
    val _43_const = __b__.loadMtdSymbol(_17_TestDSL2_Sym, "const", scala.Some(0), false);
    val _44_apply = __b__.loadMtdSymbol(_36_Base_ArgsVarargs_Sym, "apply", scala.Some(0), false);
    val _45_mapp = __b__.loadMtdSymbol(_17_TestDSL2_Sym, "mapp", scala.Some(0), false);
    val _46_wrapConstruct = __b__.loadMtdSymbol(_17_TestDSL2_Sym, "wrapConstruct", scala.Some(0), false);
    val _47_internal_u0020IR = __b__.loadMtdSymbol(_17_TestDSL2_Sym, "internal$u0020IR", scala.Some(0), false);
    {
      val _$__b__ = __b__.bindVal("__b__", _0_TestDSL2);
      __b__.letin(_$__b__, __b__.mapp(__b__.module(_1_TestDSL2, "Quasicodes", _3_QuasiBase_Quasicodes_), _4_qcbase, _0_TestDSL2)()(), __b__.mapp(__b__.mapp(__b__.module(_1_TestDSL2, "Quasicodes", _3_QuasiBase_Quasicodes_), _4_qcbase, _0_TestDSL2)()(), _47_internal_u0020IR, _14_QuasiBase_IR)(_11_List, _13_Object)(__b__.Args(__b__.mapp(__b__.readVal(_$__b__), _46_wrapConstruct, _16_SimpleAST_Rep)()(__b__.Args(__b__.byName({
        val _$_0_ListSym = __b__.bindVal("_0_ListSym", __b__.uninterpretedType[__b__.ScalaTypeSymbol]);
        __b__.letin(_$_0_ListSym, __b__.mapp(__b__.readVal(_$__b__), _18_loadTypSymbol, __b__.uninterpretedType[__b__.ScalaTypeSymbol])()(__b__.Args(__b__.const("scala.collection.immutable.List"))), {
          val _$_1_immutable = __b__.bindVal("_1_immutable", _16_SimpleAST_Rep);
          __b__.letin(_$_1_immutable, __b__.mapp(__b__.readVal(_$__b__), _19_moduleObject, _16_SimpleAST_Rep)()(__b__.Args(__b__.const("scala.collection.immutable"), __b__.const(true))), {
            val _$_2_intSym = __b__.bindVal("_2_intSym", __b__.uninterpretedType[__b__.ScalaTypeSymbol]);
            __b__.letin(_$_2_intSym, __b__.mapp(__b__.readVal(_$__b__), _18_loadTypSymbol, __b__.uninterpretedType[__b__.ScalaTypeSymbol])()(__b__.Args(__b__.const("int"))), {
              val _$_3_scala = __b__.bindVal("_3_scala", _16_SimpleAST_Rep);
              __b__.letin(_$_3_scala, __b__.mapp(__b__.readVal(_$__b__), _19_moduleObject, _16_SimpleAST_Rep)()(__b__.Args(__b__.const("scala"), __b__.const(true))), {
                val _$_4_int = __b__.bindVal("_4_int", _21_ScalaTyping_TypeRep);
                __b__.letin(_$_4_int, __b__.mapp(__b__.readVal(_$__b__), _23_typeApp, _21_ScalaTyping_TypeRep)()(__b__.Args(__b__.readVal(_$_3_scala), __b__.readVal(_$_2_intSym), _22_Nil)), {
                  val _$_5_List = __b__.bindVal("_5_List", _21_ScalaTyping_TypeRep);
                  __b__.letin(_$_5_List, __b__.mapp(__b__.readVal(_$__b__), _23_typeApp, _21_ScalaTyping_TypeRep)()(__b__.Args(__b__.readVal(_$_1_immutable), __b__.readVal(_$_0_ListSym), __b__.mapp(_25_List, _27_apply, _24_List)(_21_ScalaTyping_TypeRep)(__b__.ArgsVarargs(__b__.Args(), __b__.Args(__b__.readVal(_$_4_int)))))), {
                    val _$_6_List = __b__.bindVal("_6_List", _16_SimpleAST_Rep);
                    __b__.letin(_$_6_List, __b__.mapp(__b__.readVal(_$__b__), _19_moduleObject, _16_SimpleAST_Rep)()(__b__.Args(__b__.const("scala.collection.immutable.List"), __b__.const(false))), {
                      val _$_7_List_Sym = __b__.bindVal("_7_List_Sym", __b__.uninterpretedType[__b__.ScalaTypeSymbol]);
                      __b__.letin(_$_7_List_Sym, __b__.mapp(__b__.readVal(_$__b__), _18_loadTypSymbol, __b__.uninterpretedType[__b__.ScalaTypeSymbol])()(__b__.Args(__b__.const("scala.collection.immutable.List$"))), {
                        val _$_8_apply = __b__.bindVal("_8_apply", __b__.uninterpretedType[__b__.MtdSymbol] /** passing a tag here solves the issue */ );
                        __b__.letin(_$_8_apply, __b__.mapp(__b__.readVal(_$__b__), _33_loadMtdSymbol, __b__.uninterpretedType[__b__.MtdSymbol] /** passing a tag here solves the issue */ )()(__b__.Args(__b__.readVal(_$_7_List_Sym), __b__.const("apply"), __b__.mapp(_30_Some, _32_apply, _29_Some)(_10_int)(__b__.Args(__b__.const(0))), __b__.const(false))), __b__.mapp(__b__.readVal(_$__b__), _45_mapp, _16_SimpleAST_Rep)()(__b__.Args(__b__.readVal(_$_6_List), __b__.readVal(_$_8_apply), __b__.readVal(_$_5_List)), __b__.ArgsVarargs(__b__.Args(), __b__.Args(__b__.readVal(_$_4_int))), __b__.ArgsVarargs(__b__.Args(), __b__.Args(__b__.mapp(__b__.module(__b__.readVal(_$__b__), "ArgsVarargs", _37_Base_ArgsVarargs_), _44_apply, _35_Base_ArgsVarargs)()(__b__.Args(__b__.mapp(__b__.module(__b__.readVal(_$__b__), "Args", _41_Base_Args_), _42_apply, _39_Base_Args)()(__b__.ArgsVarargs(__b__.Args(), __b__.Args())), __b__.mapp(__b__.module(__b__.readVal(_$__b__), "Args", _41_Base_Args_), _42_apply, _39_Base_Args)()(__b__.ArgsVarargs(__b__.Args(), __b__.Args(__b__.mapp(__b__.readVal(_$__b__), _43_const, _16_SimpleAST_Rep)()(__b__.Args(__b__.const(1))))))))))), _16_SimpleAST_Rep)
                      }, _16_SimpleAST_Rep)
                    }, _16_SimpleAST_Rep)
                  }, _16_SimpleAST_Rep)
                }, _16_SimpleAST_Rep)
              }, _16_SimpleAST_Rep)
            }, _16_SimpleAST_Rep)
          }, _16_SimpleAST_Rep)
        }, _16_SimpleAST_Rep)
      }))))), _14_QuasiBase_IR)
    }
  }))
}.run)*/


