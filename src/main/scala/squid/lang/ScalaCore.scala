// Copyright 2017 EPFL DATA Lab (data.epfl.ch)
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package squid
package lang

import squid.quasi.mirror
import squid.quasi.dbg_mirror

trait ScalaCore
  extends Base
  // ---
  with UnitMirror
  with NullMirror
  with BooleanMirror
  with IntMirror
  with DoubleMirror
  with StringMirror
  // ---
  with OptionMirror
  with EitherMirror
  with FunctionMirror
  // ---
  with Tuple2Mirror
  with Tuple3Mirror
  with Tuple4Mirror
  with Tuple5Mirror
  // ---
  with SquidLibMirror
  with VarMirror
  with PredefMirror

@mirror[Unit] trait UnitMirror
@mirror[Null] trait NullMirror
@mirror[Boolean] trait BooleanMirror
@mirror[Int] trait IntMirror
@mirror[Double] trait DoubleMirror
@mirror[String] trait StringMirror

@mirror[Option[_]] trait OptionMirror
@mirror[Either[_,_]] trait EitherMirror
@mirror[Function[_,_]] trait FunctionMirror

@mirror[Tuple2[_,_]] trait Tuple2Mirror
@mirror[Tuple3[_,_,_]] trait Tuple3Mirror
@mirror[Tuple4[_,_,_,_]] trait Tuple4Mirror
@mirror[Tuple5[_,_,_,_,_]] trait Tuple5Mirror

@mirror[squid.lib.`package`.type] trait SquidLibMirror
@mirror[squid.lib.MutVar[_]] trait VarMirror
@mirror[Predef.type] trait PredefMirror

