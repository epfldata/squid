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

package object squid {
  
  /** Returns anything you ever wished for... */
  def genie[T]: T = {
    ??? // genies don't exist :-(
  }
  
  /** To test for ad-hoc warnings printed on stderr.
    * Note: not ideal, as it can result in nondeterministic test failures when tests are ran in parallel by SBT. */
  def captureStdErr(thunk: => Unit): String = {
    val oldStrErr = System.err
    val newStdErr = new java.io.ByteArrayOutputStream()
    System.setErr(new java.io.PrintStream(newStdErr,true))
    thunk
    System.setErr(oldStrErr)
    newStdErr.toString
  }
  
}

