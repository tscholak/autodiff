name := "autodiff"

version := "0.1"

scalaVersion := "2.12.3-bin-typelevel-4"
scalaOrganization := "org.typelevel"

scalacOptions ++= Seq(
  "-encoding",
  "UTF-8",
  "-feature",
  "-deprecation",
  "-unchecked",
  "-language:implicitConversions",
  "-language:higherKinds",
  "-language:existentials",
  "-language:postfixOps",
  "-language:reflectiveCalls",
  "-target:jvm-1.8",
  // "-Xfatal-warnings",
  "-Xfuture",
  "-Yno-adapted-args",
  "-Yno-imports",
  "-Ydelambdafy:method",
  "-Ypartial-unification",
  "-Yliteral-types",
  "-Ywarn-unused-import",
  "-Ywarn-dead-code",
  "-Ywarn-numeric-widen",
  "-Ywarn-value-discard",
  "-Ypatmat-exhaust-depth",
  "80"
)

wartremoverWarnings in (Compile, compile) ++= Warts.allBut(
  Wart.Any,
  Wart.AsInstanceOf,
  Wart.Equals,
  Wart.ExplicitImplicitTypes, // - see puffnfresh/wartremover#226
  Wart.ImplicitConversion, // - see puffnfresh/wartremover#242
  Wart.IsInstanceOf,
  // Wart.NoNeedForMonad, // - see puffnfresh/wartremover#159
  Wart.Nothing,
  Wart.Overloading,
  Wart.Product, // _ these two are highly correlated
  Wart.Serializable, // /
  Wart.ToString,
  Wart.PublicInference
)

val scalazVersion = "7.2.+"
val monocleVersion = "1.4.+"
val simulacrumVersion = "0.10.+"
val matryoshkaVersion = "0.21.+"

libraryDependencies ++= Seq(
  "org.scalaz" %% "scalaz-core" % scalazVersion,
  "com.github.julien-truffaut" %% "monocle-core" % monocleVersion,
  "com.github.julien-truffaut" %% "monocle-macro" % monocleVersion,
  "com.github.julien-truffaut" %% "monocle-law" % monocleVersion % "test",
  "com.github.mpilquist" %% "simulacrum" % simulacrumVersion,
  "com.slamdata" %% "matryoshka-core" % matryoshkaVersion
)

addCompilerPlugin("org.spire-math" %% "kind-projector" % "0.9.4")
addCompilerPlugin("org.scalamacros" %% "paradise" % "2.1.0" cross CrossVersion.patch)

resolvers ++= Seq(
  Resolver.bintrayRepo("non", "maven"),
  Resolver.sonatypeRepo("public")
)

cancelable in Global := true
