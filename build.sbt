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

val paradiseVersion = "2.1.0"
val squidVersion = "0.3.0-SNAPSHOT"
val squidIsSnapshot: Boolean = squidVersion endsWith "-SNAPSHOT"

lazy val commonSettings = Seq(
  version := squidVersion,
  scalaVersion := "2.11.11",
  organization := "ch.epfl.data",
  autoCompilerPlugins := true,
  scalacOptions ++= Seq("-feature", "-language:implicitConversions", "-language:higherKinds", "-language:postfixOps"
    , "-deprecation"
  ),
  incOptions := incOptions.value.withLogRecompileOnMacro(false), // silences macro-related recompilation messages (cf. https://github.com/sbt/zinc/issues/142)
  resolvers += Resolver.sonatypeRepo("snapshots"),
  resolvers += Resolver.sonatypeRepo("releases"),
  addCompilerPlugin("org.scalamacros" % "paradise" % paradiseVersion cross CrossVersion.full),
  libraryDependencies ++= Seq(
    "junit" % "junit-dep" % "4.10" % "test",
    "org.scalatest" % "scalatest_2.11" % "2.2.0" % "test"
  ),
  libraryDependencies ++= (
      if (scalaVersion.value.startsWith("2.10")) List("org.scalamacros" %% "quasiquotes" % paradiseVersion)
      else Nil
    ),
  libraryDependencies += "com.lihaoyi" % "ammonite" % "1.0.3" % "test" cross CrossVersion.full,
  // For the ammonite REPL:
  sourceGenerators in Test += Def.task {
    val file = (sourceManaged in Test).value / "amm.scala"
    IO.write(file, """object amm extends App { ammonite.Main().run() }""")
    Seq(file)
  }.taskValue
) ++ publishSettings
lazy val scalaReflect = Def.setting { "org.scala-lang" % "scala-reflect" % scalaVersion.value }
lazy val scalaCompiler = Def.setting { "org.scala-lang" % "scala-compiler" % scalaVersion.value }

lazy val main = (project in file(".")).
  dependsOn(core).
  dependsOn(core % "test->test").
  settings(commonSettings: _*).
  settings(
    name := "squid"
  )

lazy val core = (project in file("core")).
  dependsOn(core_macros).
  settings(commonSettings: _*).
  settings(
    name := "squid-core",
    libraryDependencies += scalaReflect.value,
    libraryDependencies += scalaCompiler.value,
    // other settings here
    //libraryDependencies += "ch.epfl.lamp" % "scala-yinyang_2.11" % "0.2.0-SNAPSHOT",
    libraryDependencies += scalaVersion("org.scala-lang" % "scala-reflect" % _).value,
    libraryDependencies += scalaVersion("org.scala-lang" % "scala-library" % _).value,
    libraryDependencies += scalaVersion("org.scala-lang" % "scala-compiler" % _).value,
    publishArtifact in packageDoc := false // otherwise compiler crashes while trying to gen doc (java.util.NoSuchElementException: next on empty iterator)
  )

lazy val core_macros = (project in file("core_macros")).
  settings(commonSettings: _*).
  settings(
    name := "squid-core-macros",
    libraryDependencies += scalaVersion("org.scala-lang" % "scala-reflect" % _).value
  )


val SCVersion = "0.1.4-SNAPSHOT"

lazy val scBackendMacros = (project in file("sc-backend/macros")).
  settings(commonSettings: _*).
  settings(
    name := "squid-sc-backend-macros",
    libraryDependencies ++= Seq("ch.epfl.data" % "sc-pardis-compiler_2.11" % SCVersion)
  ).
  dependsOn(main)
lazy val scBackend = (project in file("sc-backend")).
  dependsOn(scBackendMacros).
  dependsOn(main % "test->test").
  settings(commonSettings: _*).
  settings(
    name := "squid-sc-backend",
    libraryDependencies ++= Seq("ch.epfl.data" % "sc-pardis-compiler_2.11" % SCVersion)
  )


lazy val example = (project in file("example")).
  settings(commonSettings: _*).
  settings(
    name := "squid-example",
    parallelExecution in Test := false
  ).
  dependsOn(main).
  dependsOn(main % "test->test")

val developers = 
      <developers>
        <developer>
          <id>LPTK</id>
          <name>Lionel Parreaux</name>
          <url>http://people.epfl.ch/lionel.parreaux</url>          
        </developer>
      </developers>

lazy val publishSettings = Seq(
  // resolvers += Resolver.sonatypeRepo("releases"),
  publishMavenStyle := true,
  isSnapshot := squidIsSnapshot,
  publishTo := {
    val nexus = "https://oss.sonatype.org/"
    if (isSnapshot.value)
      Some("snapshots" at nexus + "content/repositories/snapshots")
    else
      Some("releases"  at nexus + "service/local/staging/deploy/maven2")
  },
  publishArtifact in (Compile, packageSrc) := false,
  pomIncludeRepository := { _ => false },
  pomExtra := developers,
  publishArtifact in Test := false,
  publishArtifact in packageDoc := !squidIsSnapshot // publishing doc is super slow -- don't do it for snapshots to ease development
)
