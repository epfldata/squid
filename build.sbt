// Copyright 2018 EPFL DATA Lab (data.epfl.ch)
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

val scala211Version = "2.11.12"
val scala212Version = "2.12.10"
val scala213Version = "2.13.6"

val paradiseVersion = "2.1.0"
val squidVersion = "0.4.1-SNAPSHOT"
val squidIsSnapshot: Boolean = squidVersion endsWith "-SNAPSHOT"

val initialConsoleCommands = "import squid.IR, IR.Predef._, IR.Quasicodes._"

// def compileWithMacroParadise: Command = Command.command("compileWithMacroParadise") { state =>
//   import Project._
//   val extractedState = extract(state)
//   val stateWithMacroParadise = CrossVersion.partialVersion(extractedState.get(scalaVersion)) match {
//     case Some((2, n)) if n >= 13 => extractedState.appendWithSession(Seq(Compile / scalacOptions += "-Ymacro-annotations"), state)
//     case _ => extractedState.appendWithSession(addCompilerPlugin("org.scalamacros" % "paradise" % "2.1.1" cross CrossVersion.full), state)
//   }
//   val (stateAfterCompileWithMacroParadise, _) = extract(stateWithMacroParadise).runTask(Compile / compile, stateWithMacroParadise)
//   stateAfterCompileWithMacroParadise
// }

lazy val commonSettings = Seq(
  version := squidVersion,
  scalaVersion := scala212Version, // default Scala version
  crossScalaVersions := Seq(scala211Version, scala212Version, scala213Version),
  organization := "ch.epfl.data",
  autoCompilerPlugins := true,
  scalacOptions ++= Seq("-feature", "-language:implicitConversions", "-language:higherKinds", "-language:postfixOps"
    , "-deprecation", "-unchecked"
    //, "-Ybackend-parallelism", "4" // does not seem to result in noticeable improvements of compile time,
                                     // as measured by repeatedly doing ";reload ;clean ;test:clean ;test:compile" in
                                     // sbt, which is reported to take around "Total time: 48 s"
  ),
  incOptions := incOptions.value.withLogRecompileOnMacro(false), // silences macro-related recompilation messages (cf. https://github.com/sbt/zinc/issues/142)
  parallelExecution in Test := false,
  resolvers += Resolver.sonatypeRepo("snapshots"),
  resolvers += Resolver.sonatypeRepo("releases"),
  // addCompilerPlugin("org.scalamacros" % "paradise" % paradiseVersion cross CrossVersion.full),
  // addCompilerPlugin("org.scalamacros" % "paradise" % "2.1.0" cross CrossVersion.full),
  // commands += compileWithMacroParadise,
  // addCommandAlias("compile", "compileWithMacroParadise"),
  
  unmanagedSources in Compile := (unmanagedSources in Compile).value.filterNot(_.getPath.contains("_perso")),
  // libraryDependencies += "org.scalactic" %% "scalactic" % "3.0.5",
  libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.9" % "test",
  libraryDependencies += "com.lihaoyi" %% "sourcecode" % "0.2.7",
  libraryDependencies += "eu.timepit" %% "singleton-ops" % "0.5.0",
  libraryDependencies += "com.chuusai" %% "shapeless" % "2.3.3",
  
  //libraryDependencies += "com.lihaoyi" % "ammonite" % "1.1.2" % "test" cross CrossVersion.full,
  //// For the ammonite REPL:
  //sourceGenerators in Test += Def.task {
  //  val file = (sourceManaged in Test).value / "amm.scala"
  //  IO.write(file, """object amm extends App { ammonite.Main().run() }""")
  //  Seq(file)
  //}.taskValue,
  
) ++ publishSettings //++ addCommandAlias("compile", "compileWithMacroParadise")
// ++ {
//   if (scalaVersion.value.startsWith("2.11") || scalaVersion.value.startsWith("2.12"))
//     addCompilerPlugin("org.scalamacros" % "paradise" % paradiseVersion cross CrossVersion.full) :: Nil
//   else Nil
// }

lazy val main = (project in file(".")).
  dependsOn(core).
  dependsOn(core % "test->test").
  settings(commonSettings: _*).
  settings(
    name := "squid",
    initialCommands in console := initialConsoleCommands,
  )

lazy val core = (project in file("core")).
  dependsOn(core_macros).
  settings(commonSettings: _*)//.commands(compileWithMacroParadise)
  .
  settings(
    name := "squid-core",
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


lazy val example = (project in file("example")).
  settings(commonSettings: _*).
  settings(
    name := "squid-example",
    parallelExecution in Test := false,
    initialCommands in console := initialConsoleCommands,
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

import microsites.ExtraMdFileConfig

val makeMicrositeNoTut: TaskKey[Unit] = taskKey[Unit]("Main Task to build a Microsite")
val makeMicrositeQuick: TaskKey[Unit] = taskKey[Unit]("Main Task to build a Microsite")

lazy val micrositeSettings = Seq(
  micrositeName := "Squid",
  micrositeDescription := "Squid ― type-safe metaprogramming for Scala",
  micrositeAuthor := "Lionel Parreaux (@lptk)",
  micrositeBaseUrl := "/squid",
  micrositeDocumentationUrl := "/squid/reference",
  micrositeGithubOwner := "epfldata",
  micrositeGithubRepo := "squid",
  micrositeGitterChannel := true,
  micrositeGitterChannelUrl := "epfldata-squid/Lobby",
  micrositeHighlightTheme := "atom-one-light",
  micrositeOrganizationHomepage := "https://data.epfl.ch/",
  includeFilter in makeSite := "*.html" | "*.css" | "*.png" | "*.jpg" | "*.gif" | "*.js" | "*.swf" | "*.yml" | "*.md" | "*.svg",
  micrositeCssDirectory := (resourceDirectory in Compile).value / "microsite" / "styles",
  micrositeJsDirectory := (resourceDirectory in Compile).value / "microsite" / "js",
  fork in tut := true,
  git.remoteRepo := "git@github.com:epfldata/squid.git",
  micrositeExtraMdFiles := Map(
    //file("CONTRIBUTING.md") -> ExtraMdFileConfig(
    //  "contributing.md",
    //  "home",
    //   Map("title" -> "Contributing", "section" -> "contributing", "position" -> "50")
    //),
    file("README.md") -> ExtraMdFileConfig(
      "home.md",
      "home",
      Map("title" -> "Home", "section" -> "home", "position" -> "0")
    )
  ),
  makeMicrositeNoTut := {
    Def
      .sequential(
        microsite,
        //tut,
        //micrositeTutExtraMdFiles,
        makeSite,
        micrositeConfig
      )
      .value
  },
  makeMicrositeQuick := {
    Def
      .sequential(
        microsite,
        tutQuick,
        //micrositeTutExtraMdFiles,
        makeSite,
        micrositeConfig
      )
      .value
  },
)

lazy val site = (project in file("site"))
  .enablePlugins(MicrositesPlugin)
  .settings(moduleName := "site")
  .settings(commonSettings)
  .settings(micrositeSettings)
  .dependsOn(example)
