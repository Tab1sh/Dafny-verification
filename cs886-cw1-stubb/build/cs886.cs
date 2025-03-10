// Dafny program Main.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
[assembly: DafnyAssembly.DafnySourceAttribute(@"// dafny 4.7.0.0
// Command-line arguments: build Main.dfy ConsoleIONative.cs --target cs --output /home/xvb24203/Downloads/cs886-cw1-stubb/build/cs886
// Main.dfy


module CS886 {
  method {:main} Main(_noArgsParameter: seq<seq<char>>)
    decreases *
  {
    REPL("">"");
  }

  method REPL(prompt: string)
    decreases *
  {
    var inGame: bool := false;
    var secret: string := """";
    var remainingTries: nat := 0;
    while true
      decreases *
    {
      print prompt + "" "";
      var resp := ReadLine();
      var cmdOpt: Maybe<CMD> := fromString(resp);
      match cmdOpt {
        case {:split false} Nothing() =>
          {
            print ""Invalid command.\n"";
            continue;
          }
        case {:split false} Just(cmd) =>
          match cmd {
            case {:split false} Quit() =>
              {
                if inGame {
                  print ""Abandoning game, goodbye\n"";
                } else {
                  print ""Exiting game\n"";
                }
                break;
              }
            case {:split false} Help() =>
              {
                print ""Yays & Naes\n\n"";
                print ""Commands:\n\n"";
                print "":quit         -- Exit programme\n"";
                print "":play [n] [s] -- Play a game with n tries and a secret sequence s\n"";
                print "":guess [seq]  -- guess the secret\n"";
                print "":stop         -- end game\n"";
                continue;
              }
            case {:split false} Play(n, s) =>
              {
                if inGame {
                  if resp == "":play 4 1234"" {
                    print ""Already in a game.\n"";
                  } else {
                    print ""Invalid command.\n"";
                  }
                } else {
                  if n < 4 || hasDuplicates(s) {
                    print ""Invalid command.\n"";
                  } else if |s| < 4 {
                    print ""The secret is too short.\n"";
                  } else {
                    inGame := true;
                    remainingTries := n;
                    secret := s;
                    print ""Game on!\n"";
                  }
                }
                continue;
              }
            case {:split false} Guess(g) =>
              {
                if !inGame {
                  print ""Not in a game.\n"";
                } else if |g| != |secret| {
                  print ""Invalid command.\n"";
                } else {
                  if g == secret {
                    print ""Congratulations you guessed correctly!\n"";
                    inGame := false;
                  } else {
                    var yays := countYays(secret, g);
                    var naes := countNaes(secret, g);
                    print formatSecret(g) + "" "";
                    print yays;
                    print "" yay "";
                    print naes;
                    print "" nae\n"";
                    if remainingTries > 0 {
                      remainingTries := remainingTries - 1;
                    }
                    if remainingTries == 0 {
                      print ""No more turns left!\n"";
                      print ""The secret was: \n"" + secret + ""\n"";
                      inGame := false;
                    }
                  }
                }
                continue;
              }
            case {:split false} Stop() =>
              {
                if !inGame {
                  print ""Not in a game.\n"";
                } else {
                  inGame := false;
                  print ""Abandoning game, resetting state.\n"";
                }
                continue;
              }
          }
      }
    }
  }

  function hasDuplicates(s: string): bool
    decreases s
  {
    exists i: int, j: int {:trigger s[j], s[i]} :: 
      0 <= i < j < |s| &&
      s[i] == s[j]
  }

  function firstDuplicate(s: string): char
    requires exists i: int, j: int {:trigger s[j], s[i]} :: 0 <= i < j < |s| && s[i] == s[j]
    decreases s
  {
    s[0]
  }

  function contains(s: string, c: char): bool
    decreases s, c
  {
    exists i: int {:trigger s[i]} :: 
      0 <= i < |s| &&
      s[i] == c
  }

  function countYays(secret: string, guess: string): nat
    requires |secret| == |guess|
    decreases secret, guess
  {
    if |secret| == 0 then
      0
    else
      (if secret[0] == guess[0] then 1 else 0) + countYays(secret[1..], guess[1..])
  }

  function countCommon(secret: string, guess: string): nat
    decreases secret, guess
  {
    if guess == """" then
      0
    else
      (if contains(secret, guess[0]) then 1 else 0) + countCommon(secret, guess[1..])
  }

  function countNaes(secret: string, guess: string): nat
    requires |secret| == |guess|
    decreases secret, guess
  {
    var common: nat := countCommon(secret, guess);
    var yays: nat := countYays(secret, guess);
    if common >= yays then
      common - yays
    else
      0
  }

  function formatSecret(s: string): string
    decreases s
  {
    if |s| == 0 then
      ""[]""
    else
      ""["" + s[0 .. 1] + formatSecretRec(s, 1) + ""]""
  }

  function formatSecretRec(s: string, i: nat): string
    decreases |s| - i
  {
    if i >= |s| then
      """"
    else
      "", "" + s[i .. i + 1] + formatSecretRec(s, i + 1)
  }

  import opened IO = Common.IO

  import opened Data = Common.Data

  import opened String = Common.Data.String

  import opened Maybe = Common.Data.Maybe

  import opened Result = Common.Data.Result

  import opened Commands

  import opened ConsoleIO
}

module {:extern ""ConsoleIO""} ConsoleIO {
  method {:extern ""INTERNAL__WriteLine""} WriteLine(line: string)
    decreases line

  method {:extern ""INTERNAL__ReadLine""} ReadLine() returns (line: string)
}

module Commands {
  function processQuit(cmd: string, args: seq<string>): Maybe<CMD>
    decreases cmd, args
  {
    if cmd == ""quit"" then
      Maybe.Just(Quit)
    else
      Maybe.Nothing
  }

  function processHelp(cmd: string, args: seq<string>): Maybe<CMD>
    decreases cmd, args
  {
    if cmd == ""help"" || cmd == ""h"" || cmd == ""?"" then
      Maybe.Just(Help)
    else
      Maybe.Nothing
  }

  function whenNothing<T>(m: Maybe<T>, alt: Maybe<T>): Maybe<T>
    decreases m, alt
  {
    if m != Maybe.Nothing then
      m
    else
      alt
  }

  function process(cmd: string, args: seq<string>): Maybe<CMD>
    decreases cmd, args
  {
    whenNothing(processQuit(cmd, args), processHelp(cmd, args))
  }

  function stringToNat(s: string): nat
    decreases s
  {
    if s == ""0"" then
      0
    else if s == ""1"" then
      1
    else if s == ""2"" then
      2
    else if s == ""3"" then
      3
    else if s == ""4"" then
      4
    else if s == ""5"" then
      5
    else if s == ""6"" then
      6
    else if s == ""7"" then
      7
    else if s == ""8"" then
      8
    else if s == ""9"" then
      9
    else
      0
  }

  function stripColon(s: string): Maybe<string>
    decreases s
  {
    if |s| > 0 && s[0] == ':' then
      Maybe.Just(s[1..])
    else
      Maybe.Nothing
  }

  function isWhitespace(c: char): bool
    decreases c
  {
    c == ' '
  }

  function dropLeadingSpaces(s: string): string
    decreases s
  {
    if s == """" then
      """"
    else if isWhitespace(s[0]) then
      dropLeadingSpaces(s[1..])
    else
      s
  }

  function takeWord(s: string): string
    decreases s
  {
    if s == """" || isWhitespace(s[0]) then
      """"
    else
      s[0 .. 1] + takeWord(s[1..])
  }

  function words(s: string): seq<string>
    decreases s
  {
    var s': string := dropLeadingSpaces(s);
    if s' == """" then
      []
    else
      var w: string := takeWord(s'); [w] + words(s'[|w|..])
  }

  function splitCons(ws: seq<string>): Maybe<(string, seq<string>)>
    decreases ws
  {
    if |ws| > 0 then
      Maybe.Just((ws[0], ws[1..]))
    else
      Maybe.Nothing
  }

  function preprocess(s: string): Maybe<(string, seq<string>)>
    decreases s
  {
    maybe(stripColon(s), Maybe.Nothing, (res: string) => splitCons(words(res)))
  }

  function fromString(s: string): Maybe<CMD>
    decreases s
  {
    maybe(preprocess(s), Maybe.Nothing, (pair: (string, seq<string>)) => if process(pair.0, pair.1) != Maybe.Nothing then process(pair.0, pair.1) else if pair.0 == ""stop"" then Maybe.Just(Stop) else if pair.0 == ""play"" && |pair.1| == 2 then Maybe.Just(Play(stringToNat(pair.1[0]), pair.1[1])) else if pair.0 == ""guess"" && |pair.1| == 1 then Maybe.Just(Guess(pair.1[0])) else Maybe.Nothing)
  }

  import opened Maybe = Common.Data.Maybe

  import opened Seq = Common.Data.Seq

  import opened String = Common.Data.String

  import opened Nat = Common.Data.Nat

  datatype CMD = Quit | Help | Play(n: nat, secret: string) | Guess(guess: string) | Stop
}

module Common {

  module IO {
    method PrintLn(str: string)
      decreases str
    {
      print str, ""\n"";
    }
  }

  module Data {

    module Maybe {
      function maybe<T, A>(m: Maybe<T>, def: A, k: T -> A): A
        decreases m
      {
        match m {
          case Nothing() =>
            def
          case Just(t) =>
            k(t)
        }
      }

      function whenNothing<A>(m: Maybe<A>, def: Maybe<A>): Maybe<A>
        decreases m, def
      {
        maybe(m, def, (a: A) => Just(a))
      }

      datatype Maybe<T> = Nothing | Just(t: T) {
        function fromJust(m: Maybe<T>): T
          requires Just?
          decreases this, m
        {
          t
        }
      }
    }

    module Result {
      function result<E, T, C>(r: Result<E, T>, f: E -> C, g: T -> C): C
        decreases r
      {
        match r
        case Failure(e) =>
          f(e)
        case Success(t) =>
          g(t)
      }

      datatype Result<E, T> = Failure(e: E) | Success(t: T)
    }

    module Seq {
      function count<T>(xs: seq<seq<T>>): nat
        decreases xs
      {
        if |xs| == 0 then
          0
        else
          |xs[0]| + count(xs[1..])
      }

      function fmap<A, B>(f: A -> B, xs: seq<A>): seq<B>
        ensures |xs| == |fmap(f, xs)|
        decreases xs
      {
        if |xs| == 0 then
          []
        else
          [f(xs[0])] + fmap(f, xs[1..])
      }

      function intersperse<T>(xs: seq<T>, c: T): seq<T>
        decreases xs
      {
        if |xs| == 0 then
          []
        else if |xs| == 1 then
          [xs[0]]
        else
          [xs[0], c] + intersperse(xs[1..], c)
      }

      function flatten<T>(xs: seq<seq<T>>): seq<T>
        ensures |flatten(xs)| == count(xs)
        decreases xs
      {
        if |xs| == 0 then
          []
        else
          xs[0] + flatten(xs[1..])
      }

      function splitOnHelp<T(==)>(xs: seq<T>, x: seq<T>, heap: seq<T>): seq<seq<T>>
        decreases xs, x, heap
      {
        if xs == [] then
          [heap]
        else if xs[0] in x then
          [heap] + splitOnHelp(xs[1..], x, [])
        else
          splitOnHelp(xs[1..], x, heap + [xs[0]])
      }

      function splitOn<T(==)>(xs: seq<T>, x: seq<T>): seq<seq<T>>
        decreases xs, x
      {
        splitOnHelp(xs, x, [])
      }

      function replicate<T>(cnt: nat, c: T): seq<T>
        ensures |replicate(cnt, c)| == cnt
        ensures forall k: int {:trigger replicate(cnt, c)[k]} :: 0 <= k < |replicate(cnt, c)| ==> replicate(cnt, c)[k] == c
        decreases cnt
      {
        if cnt == 0 then
          []
        else
          [c] + replicate(cnt - 1, c)
      }

      function head<T>(xs: seq<T>): Maybe<T>
        decreases xs
      {
        if xs == [] then
          Nothing
        else
          Just(xs[0])
      }

      function tail<T>(xs: seq<T>): Maybe<seq<T>>
        decreases xs
      {
        if xs == [] then
          Nothing
        else
          Just(xs[1..])
      }

      function splitCons<T>(xs: seq<T>): Maybe<(T, seq<T>)>
        decreases xs
      {
        if xs == [] then
          Nothing
        else
          Just((xs[0], xs[1..]))
      }

      function singleton<T>(xs: seq<T>): Maybe<T>
        decreases xs
      {
        if xs == [] then
          Nothing
        else if |xs| > 1 then
          Nothing
        else
          Just(xs[0])
      }

      import opened Maybe
    }

    module String {
      function splitOn(str: string, cs: string): seq<string>
        decreases str, cs
      {
        Seq.splitOn(str, cs)
      }

      function words(s: string): seq<string>
        decreases s
      {
        splitOn(s, [' '])
      }

      function wordsUn(ws: seq<string>): string
        decreases ws
      {
        flatten(intersperse(ws, "" ""))
      }

      function lines(s: string): seq<string>
        decreases s
      {
        splitOn(s, ['\n', '\r'])
      }

      function linesUn(ws: seq<string>): string
        decreases ws
      {
        flatten(intersperse(ws, ""\n""))
      }

      import opened Seq
    }

    module Nat {
      function digitFromChar(c: char): Maybe<nat>
        decreases c
      {
        match c {
          case '0' =>
            Just(0)
          case '1' =>
            Just(1)
          case '2' =>
            Just(2)
          case '3' =>
            Just(3)
          case '4' =>
            Just(4)
          case '5' =>
            Just(5)
          case '6' =>
            Just(6)
          case '7' =>
            Just(7)
          case '8' =>
            Just(8)
          case '9' =>
            Just(9)
          case x =>
            Nothing
        }
      }

      function digitsFromString(s: string): Maybe<seq<nat>>
        decreases s
      {
        if s == [] then
          Just([])
        else
          maybe(digitFromChar(s[0]), Nothing, (c: nat) => maybe(digitsFromString(s[1..]), Nothing, (cs: seq<nat>) => Just([c] + cs)))
      }

      import opened Maybe
    }
  }
}
")]

//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

// When --include-runtime is true, this file is directly prepended
// to the output program. We have to avoid these using directives in that case
// since they can only appear before any other declarations.
// The DafnyRuntime.csproj file is the only place that ISDAFNYRUNTIMELIB is defined,
// so these are only active when building the C# DafnyRuntime.dll library.
#if ISDAFNYRUNTIMELIB
using System; // for Func
using System.Numerics;
using System.Collections;
#endif

namespace DafnyAssembly {
  [AttributeUsage(AttributeTargets.Assembly)]
  public class DafnySourceAttribute : Attribute {
    public readonly string dafnySourceText;
    public DafnySourceAttribute(string txt) { dafnySourceText = txt; }
  }
}

namespace Dafny {
  using System.Collections.Generic;
  using System.Collections.Immutable;
  using System.Linq;

  // Similar to System.Text.Rune, which would be perfect to use
  // except that it isn't available in the platforms we support
  // (.NET Standard 2.0 and .NET Framework 4.5.2)
  public readonly struct Rune : IComparable, IComparable<Rune>, IEquatable<Rune> {

    private readonly uint _value;

    public Rune(int value)
      : this((uint)value) {
    }

    public Rune(uint value) {
      if (!(value < 0xD800 || (0xE000 <= value && value < 0x11_0000))) {
        throw new ArgumentException();
      }

      _value = value;
    }

    public static bool IsRune(BigInteger i) {
      return (0 <= i && i < 0xD800) || (0xE000 <= i && i < 0x11_0000);
    }

    public int Value => (int)_value;

    public bool Equals(Rune other) => this == other;

    public override bool Equals(object obj) => (obj is Rune other) && Equals(other);

    public override int GetHashCode() => Value;

    // Values are always between 0 and 0x11_0000, so overflow isn't possible
    public int CompareTo(Rune other) => this.Value - other.Value;

    int IComparable.CompareTo(object obj) {
      switch (obj) {
        case null:
          return 1; // non-null ("this") always sorts after null
        case Rune other:
          return CompareTo(other);
        default:
          throw new ArgumentException();
      }
    }

    public static bool operator ==(Rune left, Rune right) => left._value == right._value;

    public static bool operator !=(Rune left, Rune right) => left._value != right._value;

    public static bool operator <(Rune left, Rune right) => left._value < right._value;

    public static bool operator <=(Rune left, Rune right) => left._value <= right._value;

    public static bool operator >(Rune left, Rune right) => left._value > right._value;

    public static bool operator >=(Rune left, Rune right) => left._value >= right._value;

    public static explicit operator Rune(int value) => new Rune(value);
    public static explicit operator Rune(BigInteger value) => new Rune((uint)value);

    // Defined this way to be consistent with System.Text.Rune,
    // but note that Dafny will use Helpers.ToString(rune),
    // which will print in the style of a character literal instead.
    public override string ToString() {
      return char.ConvertFromUtf32(Value);
    }

    // Replacement for String.EnumerateRunes() from newer platforms
    public static IEnumerable<Rune> Enumerate(string s) {
      var sLength = s.Length;
      for (var i = 0; i < sLength; i++) {
        if (char.IsHighSurrogate(s[i])) {
          if (char.IsLowSurrogate(s[i + 1])) {
            yield return (Rune)char.ConvertToUtf32(s[i], s[i + 1]);
            i++;
          } else {
            throw new ArgumentException();
          }
        } else if (char.IsLowSurrogate(s[i])) {
          throw new ArgumentException();
        } else {
          yield return (Rune)s[i];
        }
      }
    }
  }

  public interface ISet<out T> {
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<ISet<T>> AllSubsets { get; }
    bool Contains<G>(G t);
    bool EqualsAux(ISet<object> other);
    ISet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class Set<T> : ISet<T> {
    readonly ImmutableHashSet<T> setImpl;
    readonly bool containsNull;
    Set(ImmutableHashSet<T> d, bool containsNull) {
      this.setImpl = d;
      this.containsNull = containsNull;
    }

    public static readonly ISet<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty, false);

    private static readonly TypeDescriptor<ISet<T>> _TYPE = new Dafny.TypeDescriptor<ISet<T>>(Empty);
    public static TypeDescriptor<ISet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISet<T> FromElements(params T[] values) {
      return FromCollection(values);
    }

    public static Set<T> FromISet(ISet<T> s) {
      return s as Set<T> ?? FromCollection(s.Elements);
    }

    public static Set<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public static ISet<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      if (oneMoreValue == null) {
        containsNull = true;
      } else {
        d.Add(oneMoreValue);
      }

      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public ISet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISet<U> th) {
        return th;
      } else {
        var d = ImmutableHashSet<U>.Empty.ToBuilder();
        foreach (var t in this.setImpl) {
          var u = converter(t);
          d.Add(u);
        }

        return new Set<U>(d.ToImmutable(), this.containsNull);
      }
    }

    public int Count {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public long LongCount {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public IEnumerable<T> Elements {
      get {
        if (containsNull) {
          yield return default(T);
        }

        foreach (var t in this.setImpl) {
          yield return t;
        }
      }
    }

    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".
    /// </summary>
    public IEnumerable<ISet<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list, but don't include null
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
        while (true) {
          // yield both the subset without null and, if null is in the original set, the subset with null included
          var ihs = s.ToImmutable();
          yield return new Set<T>(ihs, false);
          if (containsNull) {
            yield return new Set<T>(ihs, true);
          }

          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }

          if (i == n) {
            // we have cycled through all the subsets
            break;
          }

          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }

    public bool Equals(ISet<T> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }

      if (other == null || Count != other.Count) {
        return false;
      }

      foreach (var elmt in Elements) {
        if (!other.Contains(elmt)) {
          return false;
        }
      }

      return true;
    }

    public override bool Equals(object other) {
      if (other is ISet<T>) {
        return Equals((ISet<T>)other);
      }

      var th = this as ISet<object>;
      var oth = other as ISet<object>;
      if (th != null && oth != null) {
        // We'd like to obtain the more specific type parameter U for oth's type ISet<U>.
        // We do that by making a dynamically dispatched call, like:
        //     oth.Equals(this)
        // The hope is then that its comparison "this is ISet<U>" (that is, the first "if" test
        // above, but in the call "oth.Equals(this)") will be true and the non-virtual Equals
        // can be called. However, such a recursive call to "oth.Equals(this)" could turn
        // into infinite recursion. Therefore, we instead call "oth.EqualsAux(this)", which
        // performs the desired type test, but doesn't recurse any further.
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(ISet<object> other) {
      var s = other as ISet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (containsNull) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(default(T)) + 3);
      }

      foreach (var t in this.setImpl) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(t) + 3);
      }

      return hashCode;
    }

    public override string ToString() {
      var s = "{";
      var sep = "";
      if (containsNull) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }

      foreach (var t in this.setImpl) {
        s += sep + Dafny.Helpers.ToString(t);
        sep = ", ";
      }

      return s + "}";
    }
    public static bool IsProperSubsetOf(ISet<T> th, ISet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(ISet<T> th, ISet<T> other) {
      if (other.Count < th.Count) {
        return false;
      }
      foreach (T t in th.Elements) {
        if (!other.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(ISet<T> th, ISet<T> other) {
      ISet<T> a, b;
      if (th.Count < other.Count) {
        a = th; b = other;
      } else {
        a = other; b = th;
      }
      foreach (T t in a.Elements) {
        if (b.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public bool Contains<G>(G t) {
      return t == null ? containsNull : t is T && this.setImpl.Contains((T)(object)t);
    }
    public static ISet<T> Union(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Union(b.setImpl), a.containsNull || b.containsNull);
    }
    public static ISet<T> Intersect(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Intersect(b.setImpl), a.containsNull && b.containsNull);
    }
    public static ISet<T> Difference(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Except(b.setImpl), a.containsNull && !b.containsNull);
    }
  }

  public interface IMultiSet<out T> {
    bool IsEmpty { get; }
    int Count { get; }
    long LongCount { get; }
    BigInteger ElementCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    bool Contains<G>(G t);
    BigInteger Select<G>(G t);
    IMultiSet<T> Update<G>(G t, BigInteger i);
    bool EqualsAux(IMultiSet<object> other);
    IMultiSet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class MultiSet<T> : IMultiSet<T> {
    readonly ImmutableDictionary<T, BigInteger> dict;
    readonly BigInteger occurrencesOfNull;  // stupidly, a Dictionary in .NET cannot use "null" as a key
    MultiSet(ImmutableDictionary<T, BigInteger>.Builder d, BigInteger occurrencesOfNull) {
      dict = d.ToImmutable();
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, BigInteger>.Empty.ToBuilder(), BigInteger.Zero);

    private static readonly TypeDescriptor<IMultiSet<T>> _TYPE = new Dafny.TypeDescriptor<IMultiSet<T>>(Empty);
    public static TypeDescriptor<IMultiSet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static MultiSet<T> FromIMultiSet(IMultiSet<T> s) {
      return s as MultiSet<T> ?? FromCollection(s.Elements);
    }
    public static MultiSet<T> FromElements(params T[] values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          if (!d.TryGetValue(t, out var i)) {
            i = BigInteger.Zero;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }

    public static MultiSet<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          if (!d.TryGetValue(t,
                out var i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }

    public static MultiSet<T> FromSeq(ISequence<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (var t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          if (!d.TryGetValue(t,
                out var i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }
    public static MultiSet<T> FromSet(ISet<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values.Elements) {
        if (t == null) {
          containsNull = true;
        } else {
          d[t] = BigInteger.One;
        }
      }
      return new MultiSet<T>(d, containsNull ? BigInteger.One : BigInteger.Zero);
    }
    public IMultiSet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is IMultiSet<U> th) {
        return th;
      } else {
        var d = ImmutableDictionary<U, BigInteger>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = converter(item.Key);
          d.Add(k, item.Value);
        }
        return new MultiSet<U>(d, this.occurrencesOfNull);
      }
    }

    public bool Equals(IMultiSet<T> other) {
      return IsSubsetOf(this, other) && IsSubsetOf(other, this);
    }
    public override bool Equals(object other) {
      if (other is IMultiSet<T>) {
        return Equals((IMultiSet<T>)other);
      }
      var th = this as IMultiSet<object>;
      var oth = other as IMultiSet<object>;
      if (th != null && oth != null) {
        // See comment in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(IMultiSet<object> other) {
      var s = other as IMultiSet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (occurrencesOfNull > 0) {
        var key = Dafny.Helpers.GetHashCode(default(T));
        key = (key << 3) | (key >> 29) ^ occurrencesOfNull.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
      foreach (var kv in dict) {
        var t = Dafny.Helpers.ToString(kv.Key);
        for (var i = BigInteger.Zero; i < kv.Value; i++) {
          s += sep + t;
          sep = ", ";
        }
      }
      return s + "}";
    }
    public static bool IsProperSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      if (b.occurrencesOfNull < a.occurrencesOfNull) {
        return false;
      }
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          if (b.dict[t] < a.dict[t]) {
            return false;
          }
        } else {
          if (a.dict[t] != BigInteger.Zero) {
            return false;
          }
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(IMultiSet<T> th, IMultiSet<T> other) {
      foreach (T t in th.UniqueElements) {
        if (other.Contains(t)) {
          return false;
        }
      }
      return true;
    }

    public bool Contains<G>(G t) {
      return Select(t) != 0;
    }
    public BigInteger Select<G>(G t) {
      if (t == null) {
        return occurrencesOfNull;
      }

      if (t is T && dict.TryGetValue((T)(object)t, out var m)) {
        return m;
      } else {
        return BigInteger.Zero;
      }
    }
    public IMultiSet<T> Update<G>(G t, BigInteger i) {
      if (Select(t) == i) {
        return this;
      } else if (t == null) {
        var r = dict.ToBuilder();
        return new MultiSet<T>(r, i);
      } else {
        var r = dict.ToBuilder();
        r[(T)(object)t] = i;
        return new MultiSet<T>(r, occurrencesOfNull);
      }
    }
    public static IMultiSet<T> Union(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return other;
      } else if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!r.TryGetValue(t, out var i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + a.dict[t];
      }
      foreach (T t in b.dict.Keys) {
        if (!r.TryGetValue(t, out var i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + b.dict[t];
      }
      return new MultiSet<T>(r, a.occurrencesOfNull + b.occurrencesOfNull);
    }
    public static IMultiSet<T> Intersect(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return th;
      } else if (other.IsEmpty) {
        return other;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t] < b.dict[t] ? a.dict[t] : b.dict[t]);
        }
      }
      return new MultiSet<T>(r, a.occurrencesOfNull < b.occurrencesOfNull ? a.occurrencesOfNull : b.occurrencesOfNull);
    }
    public static IMultiSet<T> Difference(IMultiSet<T> th, IMultiSet<T> other) { // \result == this - other
      if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t]);
        } else if (b.dict[t] < a.dict[t]) {
          r.Add(t, a.dict[t] - b.dict[t]);
        }
      }
      return new MultiSet<T>(r, b.occurrencesOfNull < a.occurrencesOfNull ? a.occurrencesOfNull - b.occurrencesOfNull : BigInteger.Zero);
    }

    public bool IsEmpty { get { return occurrencesOfNull == 0 && dict.IsEmpty; } }

    public int Count {
      get { return (int)ElementCount; }
    }
    public long LongCount {
      get { return (long)ElementCount; }
    }

    public BigInteger ElementCount {
      get {
        // This is inefficient
        var c = occurrencesOfNull;
        foreach (var item in dict) {
          c += item.Value;
        }
        return c;
      }
    }

    public IEnumerable<T> Elements {
      get {
        for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
          yield return default(T);
        }
        foreach (var item in dict) {
          for (var i = BigInteger.Zero; i < item.Value; i++) {
            yield return item.Key;
          }
        }
      }
    }

    public IEnumerable<T> UniqueElements {
      get {
        if (!occurrencesOfNull.IsZero) {
          yield return default(T);
        }
        foreach (var key in dict.Keys) {
          if (dict[key] != 0) {
            yield return key;
          }
        }
      }
    }
  }

  public interface IMap<out U, out V> {
    int Count { get; }
    long LongCount { get; }
    ISet<U> Keys { get; }
    ISet<V> Values { get; }
    IEnumerable<IPair<U, V>> ItemEnumerable { get; }
    bool Contains<G>(G t);
    /// <summary>
    /// Returns "true" iff "this is IMap<object, object>" and "this" equals "other".
    /// </summary>
    bool EqualsObjObj(IMap<object, object> other);
    IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter);
  }

  public class Map<U, V> : IMap<U, V> {
    readonly ImmutableDictionary<U, V> dict;
    readonly bool hasNullKey;  // true when "null" is a key of the Map
    readonly V nullValue;  // if "hasNullKey", the value that "null" maps to

    private Map(ImmutableDictionary<U, V>.Builder d, bool hasNullKey, V nullValue) {
      dict = d.ToImmutable();
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty.ToBuilder(), false, default(V));

    private Map(ImmutableDictionary<U, V> d, bool hasNullKey, V nullValue) {
      dict = d;
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }

    private static readonly TypeDescriptor<IMap<U, V>> _TYPE = new Dafny.TypeDescriptor<IMap<U, V>>(Empty);
    public static TypeDescriptor<IMap<U, V>> _TypeDescriptor() {
      return _TYPE;
    }

    public static Map<U, V> FromElements(params IPair<U, V>[] values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromCollection(IEnumerable<IPair<U, V>> values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromIMap(IMap<U, V> m) {
      return m as Map<U, V> ?? FromCollection(m.ItemEnumerable);
    }
    public IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter) {
      if (this is IMap<UU, VV> th) {
        return th;
      } else {
        var d = ImmutableDictionary<UU, VV>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = keyConverter(item.Key);
          var v = valueConverter(item.Value);
          d.Add(k, v);
        }
        return new Map<UU, VV>(d, this.hasNullKey, (VV)(object)this.nullValue);
      }
    }
    public int Count {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }
    public long LongCount {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }

    public bool Equals(IMap<U, V> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }

      if (other == null || LongCount != other.LongCount) {
        return false;
      }

      if (hasNullKey) {
        if (!other.Contains(default(U)) || !object.Equals(nullValue, Select(other, default(U)))) {
          return false;
        }
      }

      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Select(other, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public bool EqualsObjObj(IMap<object, object> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }
      if (!(this is IMap<object, object>) || other == null || LongCount != other.LongCount) {
        return false;
      }
      var oth = Map<object, object>.FromIMap(other);
      if (hasNullKey) {
        if (!oth.Contains(default(U)) || !object.Equals(nullValue, Map<object, object>.Select(oth, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Map<object, object>.Select(oth, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      // See comment in Set.Equals
      var m = other as IMap<U, V>;
      if (m != null) {
        return Equals(m);
      }
      var imapoo = other as IMap<object, object>;
      if (imapoo != null) {
        return EqualsObjObj(imapoo);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (hasNullKey) {
        var key = Dafny.Helpers.GetHashCode(default(U));
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(nullValue);
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(kv.Value);
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      if (hasNullKey) {
        s += sep + Dafny.Helpers.ToString(default(U)) + " := " + Dafny.Helpers.ToString(nullValue);
        sep = ", ";
      }
      foreach (var kv in dict) {
        s += sep + Dafny.Helpers.ToString(kv.Key) + " := " + Dafny.Helpers.ToString(kv.Value);
        sep = ", ";
      }
      return s + "]";
    }
    public bool Contains<G>(G u) {
      return u == null ? hasNullKey : u is U && dict.ContainsKey((U)(object)u);
    }
    public static V Select(IMap<U, V> th, U index) {
      // the following will throw an exception if "index" in not a key of the map
      var m = FromIMap(th);
      return index == null && m.hasNullKey ? m.nullValue : m.dict[index];
    }
    public static IMap<U, V> Update(IMap<U, V> th, U index, V val) {
      var m = FromIMap(th);
      var d = m.dict.ToBuilder();
      if (index == null) {
        return new Map<U, V>(d, true, val);
      } else {
        d[index] = val;
        return new Map<U, V>(d, m.hasNullKey, m.nullValue);
      }
    }

    public static IMap<U, V> Merge(IMap<U, V> th, IMap<U, V> other) {
      var a = FromIMap(th);
      var b = FromIMap(other);
      ImmutableDictionary<U, V> d = a.dict.SetItems(b.dict);
      return new Map<U, V>(d, a.hasNullKey || b.hasNullKey, b.hasNullKey ? b.nullValue : a.nullValue);
    }

    public static IMap<U, V> Subtract(IMap<U, V> th, ISet<U> keys) {
      var a = FromIMap(th);
      ImmutableDictionary<U, V> d = a.dict.RemoveRange(keys.Elements);
      return new Map<U, V>(d, a.hasNullKey && !keys.Contains<object>(null), a.nullValue);
    }

    public ISet<U> Keys {
      get {
        if (hasNullKey) {
          return Dafny.Set<U>.FromCollectionPlusOne(dict.Keys, default(U));
        } else {
          return Dafny.Set<U>.FromCollection(dict.Keys);
        }
      }
    }
    public ISet<V> Values {
      get {
        if (hasNullKey) {
          return Dafny.Set<V>.FromCollectionPlusOne(dict.Values, nullValue);
        } else {
          return Dafny.Set<V>.FromCollection(dict.Values);
        }
      }
    }

    public IEnumerable<IPair<U, V>> ItemEnumerable {
      get {
        if (hasNullKey) {
          yield return new Pair<U, V>(default(U), nullValue);
        }
        foreach (KeyValuePair<U, V> kvp in dict) {
          yield return new Pair<U, V>(kvp.Key, kvp.Value);
        }
      }
    }

    public static ISet<_System._ITuple2<U, V>> Items(IMap<U, V> m) {
      var result = new HashSet<_System._ITuple2<U, V>>();
      foreach (var item in m.ItemEnumerable) {
        result.Add(_System.Tuple2<U, V>.create(item.Car, item.Cdr));
      }
      return Dafny.Set<_System._ITuple2<U, V>>.FromCollection(result);
    }
  }

  public interface ISequence<out T> : IEnumerable<T> {
    long LongCount { get; }
    int Count { get; }
    [Obsolete("Use CloneAsArray() instead of Elements (both perform a copy).")]
    T[] Elements { get; }
    T[] CloneAsArray();
    IEnumerable<T> UniqueElements { get; }
    T Select(ulong index);
    T Select(long index);
    T Select(uint index);
    T Select(int index);
    T Select(BigInteger index);
    bool Contains<G>(G g);
    ISequence<T> Take(long m);
    ISequence<T> Take(ulong n);
    ISequence<T> Take(BigInteger n);
    ISequence<T> Drop(long m);
    ISequence<T> Drop(ulong n);
    ISequence<T> Drop(BigInteger n);
    ISequence<T> Subsequence(long lo, long hi);
    ISequence<T> Subsequence(long lo, ulong hi);
    ISequence<T> Subsequence(long lo, BigInteger hi);
    ISequence<T> Subsequence(ulong lo, long hi);
    ISequence<T> Subsequence(ulong lo, ulong hi);
    ISequence<T> Subsequence(ulong lo, BigInteger hi);
    ISequence<T> Subsequence(BigInteger lo, long hi);
    ISequence<T> Subsequence(BigInteger lo, ulong hi);
    ISequence<T> Subsequence(BigInteger lo, BigInteger hi);
    bool EqualsAux(ISequence<object> other);
    ISequence<U> DowncastClone<U>(Func<T, U> converter);
    string ToVerbatimString(bool asLiteral);
  }

  public abstract class Sequence<T> : ISequence<T> {
    public static readonly ISequence<T> Empty = new ArraySequence<T>(new T[0]);

    private static readonly TypeDescriptor<ISequence<T>> _TYPE = new Dafny.TypeDescriptor<ISequence<T>>(Empty);
    public static TypeDescriptor<ISequence<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISequence<T> Create(BigInteger length, System.Func<BigInteger, T> init) {
      var len = (int)length;
      var builder = ImmutableArray.CreateBuilder<T>(len);
      for (int i = 0; i < len; i++) {
        builder.Add(init(new BigInteger(i)));
      }
      return new ArraySequence<T>(builder.MoveToImmutable());
    }
    public static ISequence<T> FromArray(T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromElements(params T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<char> FromString(string s) {
      return new ArraySequence<char>(s.ToCharArray());
    }
    public static ISequence<Rune> UnicodeFromString(string s) {
      var runes = new List<Rune>();

      foreach (var rune in Rune.Enumerate(s)) {
        runes.Add(rune);
      }
      return new ArraySequence<Rune>(runes.ToArray());
    }

    public static ISequence<ISequence<char>> FromMainArguments(string[] args) {
      Dafny.ISequence<char>[] dafnyArgs = new Dafny.ISequence<char>[args.Length + 1];
      dafnyArgs[0] = Dafny.Sequence<char>.FromString("dotnet");
      for (var i = 0; i < args.Length; i++) {
        dafnyArgs[i + 1] = Dafny.Sequence<char>.FromString(args[i]);
      }

      return Sequence<ISequence<char>>.FromArray(dafnyArgs);
    }
    public static ISequence<ISequence<Rune>> UnicodeFromMainArguments(string[] args) {
      Dafny.ISequence<Rune>[] dafnyArgs = new Dafny.ISequence<Rune>[args.Length + 1];
      dafnyArgs[0] = Dafny.Sequence<Rune>.UnicodeFromString("dotnet");
      for (var i = 0; i < args.Length; i++) {
        dafnyArgs[i + 1] = Dafny.Sequence<Rune>.UnicodeFromString(args[i]);
      }

      return Sequence<ISequence<Rune>>.FromArray(dafnyArgs);
    }

    public ISequence<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISequence<U> th) {
        return th;
      } else {
        var values = new U[this.LongCount];
        for (long i = 0; i < this.LongCount; i++) {
          var val = converter(this.Select(i));
          values[i] = val;
        }
        return new ArraySequence<U>(values);
      }
    }
    public static ISequence<T> Update(ISequence<T> sequence, long index, T t) {
      T[] tmp = sequence.CloneAsArray();
      tmp[index] = t;
      return new ArraySequence<T>(tmp);
    }
    public static ISequence<T> Update(ISequence<T> sequence, ulong index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static ISequence<T> Update(ISequence<T> sequence, BigInteger index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static bool EqualUntil(ISequence<T> left, ISequence<T> right, int n) {
      for (int i = 0; i < n; i++) {
        if (!Equals(left.Select(i), right.Select(i))) {
          return false;
        }
      }
      return true;
    }
    public static bool IsPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Count;
      return n <= right.Count && EqualUntil(left, right, n);
    }
    public static bool IsProperPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Count;
      return n < right.Count && EqualUntil(left, right, n);
    }
    public static ISequence<T> Concat(ISequence<T> left, ISequence<T> right) {
      if (left.Count == 0) {
        return right;
      }
      if (right.Count == 0) {
        return left;
      }
      return new ConcatSequence<T>(left, right);
    }
    // Make Count a public abstract instead of LongCount, since the "array size is limited to a total of 4 billion
    // elements, and to a maximum index of 0X7FEFFFFF". Therefore, as a protection, limit this to int32.
    // https://docs.microsoft.com/en-us/dotnet/api/system.array
    public abstract int Count { get; }
    public long LongCount {
      get { return Count; }
    }
    // ImmutableElements cannot be public in the interface since ImmutableArray<T> leads to a
    // "covariant type T occurs in invariant position" error. There do not appear to be interfaces for ImmutableArray<T>
    // that resolve this.
    internal abstract ImmutableArray<T> ImmutableElements { get; }

    public T[] Elements { get { return CloneAsArray(); } }

    public T[] CloneAsArray() {
      return ImmutableElements.ToArray();
    }

    public IEnumerable<T> UniqueElements {
      get {
        return Set<T>.FromCollection(ImmutableElements).Elements;
      }
    }

    public IEnumerator<T> GetEnumerator() {
      foreach (var el in ImmutableElements) {
        yield return el;
      }
    }

    IEnumerator IEnumerable.GetEnumerator() {
      return GetEnumerator();
    }

    public T Select(ulong index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(long index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(uint index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(int index) {
      return ImmutableElements[index];
    }
    public T Select(BigInteger index) {
      return ImmutableElements[(int)index];
    }
    public bool Equals(ISequence<T> other) {
      return ReferenceEquals(this, other) || (Count == other.Count && EqualUntil(this, other, Count));
    }
    public override bool Equals(object other) {
      if (other is ISequence<T>) {
        return Equals((ISequence<T>)other);
      }
      var th = this as ISequence<object>;
      var oth = other as ISequence<object>;
      if (th != null && oth != null) {
        // see explanation in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }
    public bool EqualsAux(ISequence<object> other) {
      var s = other as ISequence<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }
    public override int GetHashCode() {
      ImmutableArray<T> elmts = ImmutableElements;
      // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
      if (elmts.IsDefaultOrEmpty) {
        return 0;
      }

      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ Dafny.Helpers.GetHashCode(elmts[i]);
      }
      return hashCode;
    }
    public override string ToString() {
      if (typeof(T) == typeof(char)) {
        return string.Concat(this);
      } else {
        return "[" + string.Join(", ", ImmutableElements.Select(Dafny.Helpers.ToString)) + "]";
      }
    }

    public string ToVerbatimString(bool asLiteral) {
      var builder = new System.Text.StringBuilder();
      if (asLiteral) {
        builder.Append('"');
      }
      foreach (var c in this) {
        var rune = (Rune)(object)c;
        if (asLiteral) {
          builder.Append(Helpers.EscapeCharacter(rune));
        } else {
          builder.Append(char.ConvertFromUtf32(rune.Value));
        }
      }
      if (asLiteral) {
        builder.Append('"');
      }
      return builder.ToString();
    }

    public bool Contains<G>(G g) {
      if (g == null || g is T) {
        var t = (T)(object)g;
        return ImmutableElements.Contains(t);
      }
      return false;
    }
    public ISequence<T> Take(long m) {
      return Subsequence(0, m);
    }
    public ISequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public ISequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public ISequence<T> Drop(long m) {
      return Subsequence(m, Count);
    }
    public ISequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public ISequence<T> Drop(BigInteger n) {
      return Drop((long)n);
    }
    public ISequence<T> Subsequence(long lo, long hi) {
      if (lo == 0 && hi == Count) {
        return this;
      }
      int startingIndex = checked((int)lo);
      var length = checked((int)hi) - startingIndex;
      return new ArraySequence<T>(ImmutableArray.Create<T>(ImmutableElements, startingIndex, length));
    }
    public ISequence<T> Subsequence(long lo, ulong hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(long lo, BigInteger hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(ulong lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
  }

  internal class ArraySequence<T> : Sequence<T> {
    private readonly ImmutableArray<T> elmts;

    internal ArraySequence(ImmutableArray<T> ee) {
      elmts = ee;
    }
    internal ArraySequence(T[] ee) {
      elmts = ImmutableArray.Create<T>(ee);
    }

    internal override ImmutableArray<T> ImmutableElements {
      get {
        return elmts;
      }
    }

    public override int Count {
      get {
        return elmts.Length;
      }
    }
  }

  internal class ConcatSequence<T> : Sequence<T> {
    // INVARIANT: Either left != null, right != null, and elmts's underlying array == null or
    // left == null, right == null, and elmts's underlying array != null
    private volatile ISequence<T> left, right;
    private ImmutableArray<T> elmts;
    private readonly int count;

    internal ConcatSequence(ISequence<T> left, ISequence<T> right) {
      this.left = left;
      this.right = right;
      this.count = left.Count + right.Count;
    }

    internal override ImmutableArray<T> ImmutableElements {
      get {
        // IsDefault returns true if the underlying array is a null reference
        // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
        if (elmts.IsDefault) {
          elmts = ComputeElements();
          // We don't need the original sequences anymore; let them be
          // garbage-collected
          left = null;
          right = null;
        }
        return elmts;
      }
    }

    public override int Count {
      get {
        return count;
      }
    }

    private ImmutableArray<T> ComputeElements() {
      // Traverse the tree formed by all descendants which are ConcatSequences
      var ansBuilder = ImmutableArray.CreateBuilder<T>(count);
      var toVisit = new Stack<ISequence<T>>();
      var leftBuffer = left;
      var rightBuffer = right;
      if (left == null || right == null) {
        // elmts can't be .IsDefault while either left, or right are null
        return elmts;
      }
      toVisit.Push(rightBuffer);
      toVisit.Push(leftBuffer);

      while (toVisit.Count != 0) {
        var seq = toVisit.Pop();
        if (seq is ConcatSequence<T> cs && cs.elmts.IsDefault) {
          leftBuffer = cs.left;
          rightBuffer = cs.right;
          if (cs.left == null || cs.right == null) {
            // !cs.elmts.IsDefault, due to concurrent enumeration
            toVisit.Push(cs);
          } else {
            toVisit.Push(rightBuffer);
            toVisit.Push(leftBuffer);
          }
        } else {
          if (seq is Sequence<T> sq) {
            ansBuilder.AddRange(sq.ImmutableElements); // Optimized path for ImmutableArray
          } else {
            ansBuilder.AddRange(seq); // Slower path using IEnumerable
          }
        }
      }
      return ansBuilder.MoveToImmutable();
    }
  }

  public interface IPair<out A, out B> {
    A Car { get; }
    B Cdr { get; }
  }

  public class Pair<A, B> : IPair<A, B> {
    private A car;
    private B cdr;
    public A Car { get { return car; } }
    public B Cdr { get { return cdr; } }
    public Pair(A a, B b) {
      this.car = a;
      this.cdr = b;
    }
  }

  public class TypeDescriptor<T> {
    private readonly T initValue;
    public TypeDescriptor(T initValue) {
      this.initValue = initValue;
    }
    public T Default() {
      return initValue;
    }
  }

  public partial class Helpers {
    public static int GetHashCode<G>(G g) {
      return g == null ? 1001 : g.GetHashCode();
    }

    public static int ToIntChecked(BigInteger i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(long i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(int i, string msg) {
      return i;
    }

    public static string ToString<G>(G g) {
      if (g == null) {
        return "null";
      } else if (g is bool) {
        return (bool)(object)g ? "true" : "false";  // capitalize boolean literals like in Dafny
      } else if (g is Rune) {
        return "'" + EscapeCharacter((Rune)(object)g) + "'";
      } else {
        return g.ToString();
      }
    }

    public static string EscapeCharacter(Rune r) {
      switch (r.Value) {
        case '\n': return "\\n";
        case '\r': return "\\r";
        case '\t': return "\\t";
        case '\0': return "\\0";
        case '\'': return "\\'";
        case '\"': return "\\\"";
        case '\\': return "\\\\";
        default: return r.ToString();
      };
    }

    public static void Print<G>(G g) {
      System.Console.Write(ToString(g));
    }

    public static readonly TypeDescriptor<bool> BOOL = new TypeDescriptor<bool>(false);
    public static readonly TypeDescriptor<char> CHAR = new TypeDescriptor<char>('D');  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<Rune> RUNE = new TypeDescriptor<Rune>(new Rune('D'));  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<BigInteger> INT = new TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static readonly TypeDescriptor<BigRational> REAL = new TypeDescriptor<BigRational>(BigRational.ZERO);
    public static readonly TypeDescriptor<byte> UINT8 = new TypeDescriptor<byte>(0);
    public static readonly TypeDescriptor<ushort> UINT16 = new TypeDescriptor<ushort>(0);
    public static readonly TypeDescriptor<uint> UINT32 = new TypeDescriptor<uint>(0);
    public static readonly TypeDescriptor<ulong> UINT64 = new TypeDescriptor<ulong>(0);

    public static TypeDescriptor<T> NULL<T>() where T : class {
      return new TypeDescriptor<T>(null);
    }

    public static TypeDescriptor<A[]> ARRAY<A>() {
      return new TypeDescriptor<A[]>(new A[0]);
    }

    public static bool Quantifier<T>(IEnumerable<T> vals, bool frall, System.Predicate<T> pred) {
      foreach (var u in vals) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public static IEnumerable<bool> AllBooleans() {
      yield return false;
      yield return true;
    }
    public static IEnumerable<char> AllChars() {
      for (int i = 0; i < 0x1_0000; i++) {
        yield return (char)i;
      }
    }
    public static IEnumerable<Rune> AllUnicodeChars() {
      for (int i = 0; i < 0xD800; i++) {
        yield return new Rune(i);
      }
      for (int i = 0xE000; i < 0x11_0000; i++) {
        yield return new Rune(i);
      }
    }
    public static IEnumerable<BigInteger> AllIntegers() {
      yield return new BigInteger(0);
      for (var j = new BigInteger(1); ; j++) {
        yield return j;
        yield return -j;
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true;) {
          j--;
          yield return j;
        }
      } else if (hi == null) {
        for (var j = (BigInteger)lo; true; j++) {
          yield return j;
        }
      } else {
        for (var j = (BigInteger)lo; j < hi; j++) {
          yield return j;
        }
      }
    }
    public static IEnumerable<T> SingleValue<T>(T e) {
      yield return e;
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }

    public static U CastConverter<T, U>(T t) {
      return (U)(object)t;
    }

    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new ArraySequence<T>(array);
    }
    // In .NET version 4.5, it is possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u) {
      return u;
    }

    public static U Let<T, U>(T t, Func<T, U> f) {
      return f(t);
    }

    public static A Id<A>(A a) {
      return a;
    }

    public static void WithHaltHandling(Action action) {
      try {
        action();
      } catch (HaltException e) {
        Console.WriteLine("[Program halted] " + e.Message);
        // This is unfriendly given that Dafny's C# compiler will
        // invoke the compiled main method directly,
        // so we might be exiting the whole Dafny process here.
        // That's the best we can do until Dafny main methods support
        // a return value though (https://github.com/dafny-lang/dafny/issues/2699).
        // If we just set Environment.ExitCode here, the Dafny CLI
        // will just override that with 0.
        Environment.Exit(1);
      }
    }

    public static Rune AddRunes(Rune left, Rune right) {
      return (Rune)(left.Value + right.Value);
    }

    public static Rune SubtractRunes(Rune left, Rune right) {
      return (Rune)(left.Value - right.Value);
    }

    public static uint Bv32ShiftLeft(uint a, int amount) {
      return 32 <= amount ? 0 : a << amount;
    }
    public static ulong Bv64ShiftLeft(ulong a, int amount) {
      return 64 <= amount ? 0 : a << amount;
    }

    public static uint Bv32ShiftRight(uint a, int amount) {
      return 32 <= amount ? 0 : a >> amount;
    }
    public static ulong Bv64ShiftRight(ulong a, int amount) {
      return 64 <= amount ? 0 : a >> amount;
    }
  }

  public class BigOrdinal {
    public static bool IsLimit(BigInteger ord) {
      return ord == 0;
    }
    public static bool IsSucc(BigInteger ord) {
      return 0 < ord;
    }
    public static BigInteger Offset(BigInteger ord) {
      return ord;
    }
    public static bool IsNat(BigInteger ord) {
      return true;  // at run time, every ORDINAL is a natural number
    }
  }

  public struct BigRational {
    public static readonly BigRational ZERO = new BigRational(0);

    // We need to deal with the special case "num == 0 && den == 0", because
    // that's what C#'s default struct constructor will produce for BigRational. :(
    // To deal with it, we ignore "den" when "num" is 0.
    public readonly BigInteger num, den;  // invariant 1 <= den || (num == 0 && den == 0)

    public override string ToString() {
      if (num.IsZero || den.IsOne) {
        return string.Format("{0}.0", num);
      } else if (DividesAPowerOf10(den, out var factor, out var log10)) {
        var n = num * factor;
        string sign;
        string digits;
        if (n.Sign < 0) {
          sign = "-"; digits = (-n).ToString();
        } else {
          sign = ""; digits = n.ToString();
        }
        if (log10 < digits.Length) {
          var digitCount = digits.Length - log10;
          return string.Format("{0}{1}.{2}", sign, digits.Substring(0, digitCount), digits.Substring(digitCount));
        } else {
          return string.Format("{0}0.{1}{2}", sign, new string('0', log10 - digits.Length), digits);
        }
      } else {
        return string.Format("({0}.0 / {1}.0)", num, den);
      }
    }
    public static bool IsPowerOf10(BigInteger x, out int log10) {
      log10 = 0;
      if (x.IsZero) {
        return false;
      }
      while (true) {  // invariant: x != 0 && x * 10^log10 == old(x)
        if (x.IsOne) {
          return true;
        } else if (x % 10 == 0) {
          log10++;
          x /= 10;
        } else {
          return false;
        }
      }
    }
    /// <summary>
    /// If this method return true, then
    ///     10^log10 == factor * i
    /// Otherwise, factor and log10 should not be used.
    /// </summary>
    public static bool DividesAPowerOf10(BigInteger i, out BigInteger factor, out int log10) {
      factor = BigInteger.One;
      log10 = 0;
      if (i <= 0) {
        return false;
      }

      BigInteger ten = 10;
      BigInteger five = 5;
      BigInteger two = 2;

      // invariant: 1 <= i && i * 10^log10 == factor * old(i)
      while (i % ten == 0) {
        i /= ten;
        log10++;
      }

      while (i % five == 0) {
        i /= five;
        factor *= two;
        log10++;
      }
      while (i % two == 0) {
        i /= two;
        factor *= five;
        log10++;
      }

      return i == BigInteger.One;
    }

    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(uint n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(long n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(ulong n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    /// <summary>
    /// Construct an exact rational representation of a double value.
    /// Throw an exception on NaN or infinite values. Does not support
    /// subnormal values, though it would be possible to extend it to.
    /// </summary>
    public BigRational(double n) {
      if (Double.IsNaN(n)) {
        throw new ArgumentException("Can't convert NaN to a rational.");
      }
      if (Double.IsInfinity(n)) {
        throw new ArgumentException(
          "Can't convert +/- infinity to a rational.");
      }

      // Double-specific values
      const int exptBias = 1023;
      const ulong signMask = 0x8000000000000000;
      const ulong exptMask = 0x7FF0000000000000;
      const ulong mantMask = 0x000FFFFFFFFFFFFF;
      const int mantBits = 52;
      ulong bits = BitConverter.ToUInt64(BitConverter.GetBytes(n), 0);

      // Generic conversion
      bool isNeg = (bits & signMask) != 0;
      int expt = ((int)((bits & exptMask) >> mantBits)) - exptBias;
      var mant = (bits & mantMask);

      if (expt == -exptBias && mant != 0) {
        throw new ArgumentException(
          "Can't convert a subnormal value to a rational (yet).");
      }

      var one = BigInteger.One;
      var negFactor = isNeg ? BigInteger.Negate(one) : one;
      var two = new BigInteger(2);
      var exptBI = BigInteger.Pow(two, Math.Abs(expt));
      var twoToMantBits = BigInteger.Pow(two, mantBits);
      var mantNum = negFactor * (twoToMantBits + new BigInteger(mant));
      if (expt == -exptBias && mant == 0) {
        num = den = 0;
      } else if (expt < 0) {
        num = mantNum;
        den = twoToMantBits * exptBI;
      } else {
        num = exptBI * mantNum;
        den = twoToMantBits;
      }
    }
    public BigInteger ToBigInteger() {
      if (num.IsZero || den.IsOne) {
        return num;
      } else if (0 < num.Sign) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }

    public bool IsInteger() {
      var floored = new BigRational(this.ToBigInteger(), BigInteger.One);
      return this == floored;
    }

    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      if (a.num.IsZero) {
        aa = a.num;
        bb = b.num;
        dd = b.den;
      } else if (b.num.IsZero) {
        aa = a.num;
        dd = a.den;
        bb = b.num;
      } else {
        var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
        var xx = a.den / gcd;
        var yy = b.den / gcd;
        // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
        aa = a.num * yy;
        bb = b.num * xx;
        dd = a.den * yy;
      }
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }

      Normalize(this, that, out var aa, out var bb, out var dd);
      return aa.CompareTo(bb);
    }
    public int Sign {
      get {
        return num.Sign;
      }
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return a.CompareTo(b) > 0;
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return a.CompareTo(b) >= 0;
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      Normalize(a, b, out var aa, out var bb, out var dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      Normalize(a, b, out var aa, out var bb, out var dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num.Sign) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }

  public class HaltException : Exception {
    public HaltException(object message) : base(message.ToString()) {
    }
  }
}
// Dafny program systemModulePopulator.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

#if ISDAFNYRUNTIMELIB
using System;
using System.Numerics;
using System.Collections;
#endif
#if ISDAFNYRUNTIMELIB
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
    public static T[,] InitNewArray2<T>(T z, BigInteger size0, BigInteger size1) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      T[,] a = new T[s0,s1];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          a[i0,i1] = z;
        }
      }
      return a;
    }
    public static T[,,] InitNewArray3<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      T[,,] a = new T[s0,s1,s2];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            a[i0,i1,i2] = z;
          }
        }
      }
      return a;
    }
    public static T[,,,] InitNewArray4<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      T[,,,] a = new T[s0,s1,s2,s3];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              a[i0,i1,i2,i3] = z;
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,] InitNewArray5<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      T[,,,,] a = new T[s0,s1,s2,s3,s4];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                a[i0,i1,i2,i3,i4] = z;
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,] InitNewArray6<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      T[,,,,,] a = new T[s0,s1,s2,s3,s4,s5];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  a[i0,i1,i2,i3,i4,i5] = z;
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,] InitNewArray7<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      T[,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    a[i0,i1,i2,i3,i4,i5,i6] = z;
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,] InitNewArray8<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      T[,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      a[i0,i1,i2,i3,i4,i5,i6,i7] = z;
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,] InitNewArray9<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      T[,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        a[i0,i1,i2,i3,i4,i5,i6,i7,i8] = z;
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,] InitNewArray10<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      T[,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9] = z;
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,] InitNewArray11<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      T[,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10] = z;
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,] InitNewArray12<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      T[,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11] = z;
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,] InitNewArray13<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      T[,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12] = z;
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,,] InitNewArray14<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12, BigInteger size13) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      int s13 = (int)size13;
      T[,,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                for (int i13 = 0; i13 < s13; i13++) {
                                  a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13] = z;
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,,,] InitNewArray15<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12, BigInteger size13, BigInteger size14) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      int s13 = (int)size13;
      int s14 = (int)size14;
      T[,,,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                for (int i13 = 0; i13 < s13; i13++) {
                                  for (int i14 = 0; i14 < s14; i14++) {
                                    a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14] = z;
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,,,,] InitNewArray16<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12, BigInteger size13, BigInteger size14, BigInteger size15) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      int s13 = (int)size13;
      int s14 = (int)size14;
      int s15 = (int)size15;
      T[,,,,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                for (int i13 = 0; i13 < s13; i13++) {
                                  for (int i14 = 0; i14 < s14; i14++) {
                                    for (int i15 = 0; i15 < s15; i15++) {
                                      a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14,i15] = z;
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
  }
} // end of namespace Dafny
internal static class FuncExtensions {
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
  public static Func<U1, U2, U3, U4, UResult> DowncastClone<T1, T2, T3, T4, TResult, U1, U2, U3, U4, UResult>(this Func<T1, T2, T3, T4, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4)));
  }
  public static Func<U1, U2, U3, U4, U5, UResult> DowncastClone<T1, T2, T3, T4, T5, TResult, U1, U2, U3, U4, U5, UResult>(this Func<T1, T2, T3, T4, T5, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, TResult, U1, U2, U3, U4, U5, U6, UResult>(this Func<T1, T2, T3, T4, T5, T6, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, TResult, U1, U2, U3, U4, U5, U6, U7, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, TResult, U1, U2, U3, U4, U5, U6, U7, U8, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<U14, T14> ArgConv14, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13), ArgConv14(arg14)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<U14, T14> ArgConv14, Func<U15, T15> ArgConv15, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14, arg15) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13), ArgConv14(arg14), ArgConv15(arg15)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, U16, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, U16, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<U14, T14> ArgConv14, Func<U15, T15> ArgConv15, Func<U16, T16> ArgConv16, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14, arg15, arg16) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13), ArgConv14(arg14), ArgConv15(arg15), ArgConv16(arg16)));
  }
}
#endif
namespace _System {

  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
    public static bool _Is(BigInteger __source) {
      BigInteger _0_x = __source;
      return (_0_x).Sign != -1;
    }
  }

  public interface _ITuple2<out T0, out T1> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    _ITuple2<__T0, __T1> DowncastClone<__T0, __T1>(Func<T0, __T0> converter0, Func<T1, __T1> converter1);
  }
  public class Tuple2<T0, T1> : _ITuple2<T0, T1> {
    public readonly T0 __0;
    public readonly T1 __1;
    public Tuple2(T0 _0, T1 _1) {
      this.__0 = _0;
      this.__1 = _1;
    }
    public _ITuple2<__T0, __T1> DowncastClone<__T0, __T1>(Func<T0, __T0> converter0, Func<T1, __T1> converter1) {
      if (this is _ITuple2<__T0, __T1> dt) { return dt; }
      return new Tuple2<__T0, __T1>(converter0(__0), converter1(__1));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple2<T0, T1>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ")";
      return s;
    }
    public static _System._ITuple2<T0, T1> Default(T0 _default_T0, T1 _default_T1) {
      return create(_default_T0, _default_T1);
    }
    public static Dafny.TypeDescriptor<_System._ITuple2<T0, T1>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1) {
      return new Dafny.TypeDescriptor<_System._ITuple2<T0, T1>>(_System.Tuple2<T0, T1>.Default(_td_T0.Default(), _td_T1.Default()));
    }
    public static _ITuple2<T0, T1> create(T0 _0, T1 _1) {
      return new Tuple2<T0, T1>(_0, _1);
    }
    public static _ITuple2<T0, T1> create____hMake2(T0 _0, T1 _1) {
      return create(_0, _1);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
  }

  public interface _ITuple0 {
    _ITuple0 DowncastClone();
  }
  public class Tuple0 : _ITuple0 {
    public Tuple0() {
    }
    public _ITuple0 DowncastClone() {
      if (this is _ITuple0 dt) { return dt; }
      return new Tuple0();
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple0;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      return "()";
    }
    private static readonly _System._ITuple0 theDefault = create();
    public static _System._ITuple0 Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_System._ITuple0> _TYPE = new Dafny.TypeDescriptor<_System._ITuple0>(_System.Tuple0.Default());
    public static Dafny.TypeDescriptor<_System._ITuple0> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITuple0 create() {
      return new Tuple0();
    }
    public static _ITuple0 create____hMake0() {
      return create();
    }
    public static System.Collections.Generic.IEnumerable<_ITuple0> AllSingletonConstructors {
      get {
        yield return Tuple0.create();
      }
    }
  }

  public interface _ITuple1<out T0> {
    T0 dtor__0 { get; }
    _ITuple1<__T0> DowncastClone<__T0>(Func<T0, __T0> converter0);
  }
  public class Tuple1<T0> : _ITuple1<T0> {
    public readonly T0 __0;
    public Tuple1(T0 _0) {
      this.__0 = _0;
    }
    public _ITuple1<__T0> DowncastClone<__T0>(Func<T0, __T0> converter0) {
      if (this is _ITuple1<__T0> dt) { return dt; }
      return new Tuple1<__T0>(converter0(__0));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple1<T0>;
      return oth != null && object.Equals(this.__0, oth.__0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ")";
      return s;
    }
    public static _System._ITuple1<T0> Default(T0 _default_T0) {
      return create(_default_T0);
    }
    public static Dafny.TypeDescriptor<_System._ITuple1<T0>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0) {
      return new Dafny.TypeDescriptor<_System._ITuple1<T0>>(_System.Tuple1<T0>.Default(_td_T0.Default()));
    }
    public static _ITuple1<T0> create(T0 _0) {
      return new Tuple1<T0>(_0);
    }
    public static _ITuple1<T0> create____hMake1(T0 _0) {
      return create(_0);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
  }

  public interface _ITuple3<out T0, out T1, out T2> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    _ITuple3<__T0, __T1, __T2> DowncastClone<__T0, __T1, __T2>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2);
  }
  public class Tuple3<T0, T1, T2> : _ITuple3<T0, T1, T2> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public Tuple3(T0 _0, T1 _1, T2 _2) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
    }
    public _ITuple3<__T0, __T1, __T2> DowncastClone<__T0, __T1, __T2>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2) {
      if (this is _ITuple3<__T0, __T1, __T2> dt) { return dt; }
      return new Tuple3<__T0, __T1, __T2>(converter0(__0), converter1(__1), converter2(__2));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple3<T0, T1, T2>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ")";
      return s;
    }
    public static _System._ITuple3<T0, T1, T2> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2) {
      return create(_default_T0, _default_T1, _default_T2);
    }
    public static Dafny.TypeDescriptor<_System._ITuple3<T0, T1, T2>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2) {
      return new Dafny.TypeDescriptor<_System._ITuple3<T0, T1, T2>>(_System.Tuple3<T0, T1, T2>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default()));
    }
    public static _ITuple3<T0, T1, T2> create(T0 _0, T1 _1, T2 _2) {
      return new Tuple3<T0, T1, T2>(_0, _1, _2);
    }
    public static _ITuple3<T0, T1, T2> create____hMake3(T0 _0, T1 _1, T2 _2) {
      return create(_0, _1, _2);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
  }

  public interface _ITuple4<out T0, out T1, out T2, out T3> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    _ITuple4<__T0, __T1, __T2, __T3> DowncastClone<__T0, __T1, __T2, __T3>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3);
  }
  public class Tuple4<T0, T1, T2, T3> : _ITuple4<T0, T1, T2, T3> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public Tuple4(T0 _0, T1 _1, T2 _2, T3 _3) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
    }
    public _ITuple4<__T0, __T1, __T2, __T3> DowncastClone<__T0, __T1, __T2, __T3>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3) {
      if (this is _ITuple4<__T0, __T1, __T2, __T3> dt) { return dt; }
      return new Tuple4<__T0, __T1, __T2, __T3>(converter0(__0), converter1(__1), converter2(__2), converter3(__3));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple4<T0, T1, T2, T3>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ")";
      return s;
    }
    public static _System._ITuple4<T0, T1, T2, T3> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3);
    }
    public static Dafny.TypeDescriptor<_System._ITuple4<T0, T1, T2, T3>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3) {
      return new Dafny.TypeDescriptor<_System._ITuple4<T0, T1, T2, T3>>(_System.Tuple4<T0, T1, T2, T3>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default()));
    }
    public static _ITuple4<T0, T1, T2, T3> create(T0 _0, T1 _1, T2 _2, T3 _3) {
      return new Tuple4<T0, T1, T2, T3>(_0, _1, _2, _3);
    }
    public static _ITuple4<T0, T1, T2, T3> create____hMake4(T0 _0, T1 _1, T2 _2, T3 _3) {
      return create(_0, _1, _2, _3);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
  }

  public interface _ITuple5<out T0, out T1, out T2, out T3, out T4> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    _ITuple5<__T0, __T1, __T2, __T3, __T4> DowncastClone<__T0, __T1, __T2, __T3, __T4>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4);
  }
  public class Tuple5<T0, T1, T2, T3, T4> : _ITuple5<T0, T1, T2, T3, T4> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public Tuple5(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
    }
    public _ITuple5<__T0, __T1, __T2, __T3, __T4> DowncastClone<__T0, __T1, __T2, __T3, __T4>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4) {
      if (this is _ITuple5<__T0, __T1, __T2, __T3, __T4> dt) { return dt; }
      return new Tuple5<__T0, __T1, __T2, __T3, __T4>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple5<T0, T1, T2, T3, T4>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ")";
      return s;
    }
    public static _System._ITuple5<T0, T1, T2, T3, T4> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4);
    }
    public static Dafny.TypeDescriptor<_System._ITuple5<T0, T1, T2, T3, T4>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4) {
      return new Dafny.TypeDescriptor<_System._ITuple5<T0, T1, T2, T3, T4>>(_System.Tuple5<T0, T1, T2, T3, T4>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default()));
    }
    public static _ITuple5<T0, T1, T2, T3, T4> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      return new Tuple5<T0, T1, T2, T3, T4>(_0, _1, _2, _3, _4);
    }
    public static _ITuple5<T0, T1, T2, T3, T4> create____hMake5(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      return create(_0, _1, _2, _3, _4);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
  }

  public interface _ITuple6<out T0, out T1, out T2, out T3, out T4, out T5> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5);
  }
  public class Tuple6<T0, T1, T2, T3, T4, T5> : _ITuple6<T0, T1, T2, T3, T4, T5> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public Tuple6(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
    }
    public _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5) {
      if (this is _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> dt) { return dt; }
      return new Tuple6<__T0, __T1, __T2, __T3, __T4, __T5>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple6<T0, T1, T2, T3, T4, T5>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ")";
      return s;
    }
    public static _System._ITuple6<T0, T1, T2, T3, T4, T5> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5);
    }
    public static Dafny.TypeDescriptor<_System._ITuple6<T0, T1, T2, T3, T4, T5>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5) {
      return new Dafny.TypeDescriptor<_System._ITuple6<T0, T1, T2, T3, T4, T5>>(_System.Tuple6<T0, T1, T2, T3, T4, T5>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default()));
    }
    public static _ITuple6<T0, T1, T2, T3, T4, T5> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      return new Tuple6<T0, T1, T2, T3, T4, T5>(_0, _1, _2, _3, _4, _5);
    }
    public static _ITuple6<T0, T1, T2, T3, T4, T5> create____hMake6(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      return create(_0, _1, _2, _3, _4, _5);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
  }

  public interface _ITuple7<out T0, out T1, out T2, out T3, out T4, out T5, out T6> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6);
  }
  public class Tuple7<T0, T1, T2, T3, T4, T5, T6> : _ITuple7<T0, T1, T2, T3, T4, T5, T6> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public Tuple7(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
    }
    public _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6) {
      if (this is _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> dt) { return dt; }
      return new Tuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple7<T0, T1, T2, T3, T4, T5, T6>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ")";
      return s;
    }
    public static _System._ITuple7<T0, T1, T2, T3, T4, T5, T6> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6);
    }
    public static Dafny.TypeDescriptor<_System._ITuple7<T0, T1, T2, T3, T4, T5, T6>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6) {
      return new Dafny.TypeDescriptor<_System._ITuple7<T0, T1, T2, T3, T4, T5, T6>>(_System.Tuple7<T0, T1, T2, T3, T4, T5, T6>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default()));
    }
    public static _ITuple7<T0, T1, T2, T3, T4, T5, T6> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      return new Tuple7<T0, T1, T2, T3, T4, T5, T6>(_0, _1, _2, _3, _4, _5, _6);
    }
    public static _ITuple7<T0, T1, T2, T3, T4, T5, T6> create____hMake7(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      return create(_0, _1, _2, _3, _4, _5, _6);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
  }

  public interface _ITuple8<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7);
  }
  public class Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> : _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public Tuple8(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
    }
    public _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7) {
      if (this is _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> dt) { return dt; }
      return new Tuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ")";
      return s;
    }
    public static _System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7);
    }
    public static Dafny.TypeDescriptor<_System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7) {
      return new Dafny.TypeDescriptor<_System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7>>(_System.Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default()));
    }
    public static _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      return new Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>(_0, _1, _2, _3, _4, _5, _6, _7);
    }
    public static _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> create____hMake8(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
  }

  public interface _ITuple9<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8);
  }
  public class Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> : _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public Tuple9(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
    }
    public _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8) {
      if (this is _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> dt) { return dt; }
      return new Tuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ")";
      return s;
    }
    public static _System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8);
    }
    public static Dafny.TypeDescriptor<_System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8) {
      return new Dafny.TypeDescriptor<_System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>>(_System.Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default()));
    }
    public static _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      return new Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>(_0, _1, _2, _3, _4, _5, _6, _7, _8);
    }
    public static _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> create____hMake9(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
  }

  public interface _ITuple10<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9);
  }
  public class Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> : _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public Tuple10(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
    }
    public _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9) {
      if (this is _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> dt) { return dt; }
      return new Tuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ")";
      return s;
    }
    public static _System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9);
    }
    public static Dafny.TypeDescriptor<_System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9) {
      return new Dafny.TypeDescriptor<_System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>>(_System.Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default()));
    }
    public static _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      return new Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9);
    }
    public static _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> create____hMake10(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
  }

  public interface _ITuple11<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10);
  }
  public class Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> : _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public Tuple11(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
    }
    public _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10) {
      if (this is _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> dt) { return dt; }
      return new Tuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ")";
      return s;
    }
    public static _System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10);
    }
    public static Dafny.TypeDescriptor<_System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10) {
      return new Dafny.TypeDescriptor<_System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>>(_System.Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default()));
    }
    public static _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      return new Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10);
    }
    public static _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> create____hMake11(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
  }

  public interface _ITuple12<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11);
  }
  public class Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> : _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public Tuple12(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
    }
    public _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11) {
      if (this is _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> dt) { return dt; }
      return new Tuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ")";
      return s;
    }
    public static _System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11);
    }
    public static Dafny.TypeDescriptor<_System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11) {
      return new Dafny.TypeDescriptor<_System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>>(_System.Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default()));
    }
    public static _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      return new Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11);
    }
    public static _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> create____hMake12(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
  }

  public interface _ITuple13<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12);
  }
  public class Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> : _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public Tuple13(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
    }
    public _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12) {
      if (this is _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> dt) { return dt; }
      return new Tuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ")";
      return s;
    }
    public static _System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12);
    }
    public static Dafny.TypeDescriptor<_System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12) {
      return new Dafny.TypeDescriptor<_System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>>(_System.Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default()));
    }
    public static _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      return new Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12);
    }
    public static _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> create____hMake13(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
  }

  public interface _ITuple14<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13);
  }
  public class Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> : _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public Tuple14(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
    }
    public _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13) {
      if (this is _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> dt) { return dt; }
      return new Tuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ")";
      return s;
    }
    public static _System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13);
    }
    public static Dafny.TypeDescriptor<_System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13) {
      return new Dafny.TypeDescriptor<_System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>>(_System.Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default()));
    }
    public static _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      return new Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13);
    }
    public static _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> create____hMake14(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
  }

  public interface _ITuple15<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14);
  }
  public class Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> : _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public Tuple15(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
    }
    public _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14) {
      if (this is _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> dt) { return dt; }
      return new Tuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ")";
      return s;
    }
    public static _System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14);
    }
    public static Dafny.TypeDescriptor<_System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14) {
      return new Dafny.TypeDescriptor<_System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>>(_System.Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default()));
    }
    public static _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      return new Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14);
    }
    public static _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> create____hMake15(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
  }

  public interface _ITuple16<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15);
  }
  public class Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> : _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public Tuple16(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
    }
    public _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15) {
      if (this is _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> dt) { return dt; }
      return new Tuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ")";
      return s;
    }
    public static _System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15);
    }
    public static Dafny.TypeDescriptor<_System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15) {
      return new Dafny.TypeDescriptor<_System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>>(_System.Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default()));
    }
    public static _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      return new Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15);
    }
    public static _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> create____hMake16(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
  }

  public interface _ITuple17<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16);
  }
  public class Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> : _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public Tuple17(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
    }
    public _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16) {
      if (this is _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> dt) { return dt; }
      return new Tuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ")";
      return s;
    }
    public static _System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16);
    }
    public static Dafny.TypeDescriptor<_System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16) {
      return new Dafny.TypeDescriptor<_System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>>(_System.Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default()));
    }
    public static _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      return new Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16);
    }
    public static _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> create____hMake17(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
  }

  public interface _ITuple18<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17);
  }
  public class Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> : _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public readonly T17 __17;
    public Tuple18(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
      this.__17 = _17;
    }
    public _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17) {
      if (this is _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> dt) { return dt; }
      return new Tuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16), converter17(__17));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16) && object.Equals(this.__17, oth.__17);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__17));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__17);
      s += ")";
      return s;
    }
    public static _System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17);
    }
    public static Dafny.TypeDescriptor<_System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17) {
      return new Dafny.TypeDescriptor<_System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>>(_System.Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default()));
    }
    public static _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      return new Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17);
    }
    public static _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> create____hMake18(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
    public T17 dtor__17 {
      get {
        return this.__17;
      }
    }
  }

  public interface _ITuple19<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17, out T18> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    T18 dtor__18 { get; }
    _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18);
  }
  public class Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> : _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public readonly T17 __17;
    public readonly T18 __18;
    public Tuple19(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
      this.__17 = _17;
      this.__18 = _18;
    }
    public _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18) {
      if (this is _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> dt) { return dt; }
      return new Tuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16), converter17(__17), converter18(__18));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16) && object.Equals(this.__17, oth.__17) && object.Equals(this.__18, oth.__18);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__17));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__18));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__17);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__18);
      s += ")";
      return s;
    }
    public static _System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17, T18 _default_T18) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17, _default_T18);
    }
    public static Dafny.TypeDescriptor<_System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17, Dafny.TypeDescriptor<T18> _td_T18) {
      return new Dafny.TypeDescriptor<_System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>>(_System.Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default(), _td_T18.Default()));
    }
    public static _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      return new Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18);
    }
    public static _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> create____hMake19(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
    public T17 dtor__17 {
      get {
        return this.__17;
      }
    }
    public T18 dtor__18 {
      get {
        return this.__18;
      }
    }
  }

  public interface _ITuple20<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17, out T18, out T19> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    T18 dtor__18 { get; }
    T19 dtor__19 { get; }
    _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18, Func<T19, __T19> converter19);
  }
  public class Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> : _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public readonly T17 __17;
    public readonly T18 __18;
    public readonly T19 __19;
    public Tuple20(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
      this.__17 = _17;
      this.__18 = _18;
      this.__19 = _19;
    }
    public _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18, Func<T19, __T19> converter19) {
      if (this is _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> dt) { return dt; }
      return new Tuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16), converter17(__17), converter18(__18), converter19(__19));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16) && object.Equals(this.__17, oth.__17) && object.Equals(this.__18, oth.__18) && object.Equals(this.__19, oth.__19);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__17));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__18));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__19));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__17);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__18);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__19);
      s += ")";
      return s;
    }
    public static _System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17, T18 _default_T18, T19 _default_T19) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17, _default_T18, _default_T19);
    }
    public static Dafny.TypeDescriptor<_System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17, Dafny.TypeDescriptor<T18> _td_T18, Dafny.TypeDescriptor<T19> _td_T19) {
      return new Dafny.TypeDescriptor<_System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>>(_System.Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default(), _td_T18.Default(), _td_T19.Default()));
    }
    public static _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      return new Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19);
    }
    public static _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> create____hMake20(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
    public T17 dtor__17 {
      get {
        return this.__17;
      }
    }
    public T18 dtor__18 {
      get {
        return this.__18;
      }
    }
    public T19 dtor__19 {
      get {
        return this.__19;
      }
    }
  }
} // end of namespace _System
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
  }
} // end of namespace Dafny
internal static class FuncExtensions {
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
}
namespace Common.IO {

  public partial class __default {
    public static void PrintLn(Dafny.ISequence<Dafny.Rune> str)
    {
      Dafny.Helpers.Print((str).ToVerbatimString(false));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
    }
  }
} // end of namespace Common.IO
namespace Common.Data.Maybe {

  public partial class __default {
    public static __A maybe<__T, __A>(Common.Data.Maybe._IMaybe<__T> m, __A def, Func<__T, __A> k)
    {
      var _pat_let_tv0 = def;
      var _pat_let_tv1 = k;
      Common.Data.Maybe._IMaybe<__T> _source0 = m;
      bool unmatched0 = true;
      if (unmatched0) {
        if (_source0.is_Nothing) {
          unmatched0 = false;
          return _pat_let_tv0;
        }
      }
      if (unmatched0) {
        __T _0_t = _source0.dtor_t;
        unmatched0 = false;
        return Dafny.Helpers.Id<Func<__T, __A>>(_pat_let_tv1)(_0_t);
      }
      throw new System.Exception("unexpected control point");
    }
    public static Common.Data.Maybe._IMaybe<__A> whenNothing<__A>(Common.Data.Maybe._IMaybe<__A> m, Common.Data.Maybe._IMaybe<__A> def)
    {
      return Common.Data.Maybe.__default.maybe<__A, Common.Data.Maybe._IMaybe<__A>>(m, def, ((System.Func<__A, Common.Data.Maybe._IMaybe<__A>>)((_1_a) => {
        return Common.Data.Maybe.Maybe<__A>.create_Just(_1_a);
      })));
    }
  }

  public interface _IMaybe<T> {
    bool is_Nothing { get; }
    bool is_Just { get; }
    T dtor_t { get; }
    _IMaybe<__T> DowncastClone<__T>(Func<T, __T> converter0);
    T fromJust(Common.Data.Maybe._IMaybe<T> m);
  }
  public abstract class Maybe<T> : _IMaybe<T> {
    public Maybe() {
    }
    public static Common.Data.Maybe._IMaybe<T> Default() {
      return create_Nothing();
    }
    public static Dafny.TypeDescriptor<Common.Data.Maybe._IMaybe<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Common.Data.Maybe._IMaybe<T>>(Common.Data.Maybe.Maybe<T>.Default());
    }
    public static _IMaybe<T> create_Nothing() {
      return new Maybe_Nothing<T>();
    }
    public static _IMaybe<T> create_Just(T t) {
      return new Maybe_Just<T>(t);
    }
    public bool is_Nothing { get { return this is Maybe_Nothing<T>; } }
    public bool is_Just { get { return this is Maybe_Just<T>; } }
    public T dtor_t {
      get {
        var d = this;
        return ((Maybe_Just<T>)d)._t;
      }
    }
    public abstract _IMaybe<__T> DowncastClone<__T>(Func<T, __T> converter0);
    public T fromJust(Common.Data.Maybe._IMaybe<T> m) {
      return (this).dtor_t;
    }
  }
  public class Maybe_Nothing<T> : Maybe<T> {
    public Maybe_Nothing() : base() {
    }
    public override _IMaybe<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IMaybe<__T> dt) { return dt; }
      return new Maybe_Nothing<__T>();
    }
    public override bool Equals(object other) {
      var oth = other as Common.Data.Maybe.Maybe_Nothing<T>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Maybe.Maybe.Nothing";
      return s;
    }
  }
  public class Maybe_Just<T> : Maybe<T> {
    public readonly T _t;
    public Maybe_Just(T t) : base() {
      this._t = t;
    }
    public override _IMaybe<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IMaybe<__T> dt) { return dt; }
      return new Maybe_Just<__T>(converter0(_t));
    }
    public override bool Equals(object other) {
      var oth = other as Common.Data.Maybe.Maybe_Just<T>;
      return oth != null && object.Equals(this._t, oth._t);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._t));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Maybe.Maybe.Just";
      s += "(";
      s += Dafny.Helpers.ToString(this._t);
      s += ")";
      return s;
    }
  }
} // end of namespace Common.Data.Maybe
namespace Common.Data.Result {

  public partial class __default {
    public static __C result<__E, __T, __C>(Common.Data.Result._IResult<__E, __T> r, Func<__E, __C> f, Func<__T, __C> g)
    {
      var _pat_let_tv2 = f;
      var _pat_let_tv3 = g;
      Common.Data.Result._IResult<__E, __T> _source1 = r;
      bool unmatched1 = true;
      if (unmatched1) {
        if (_source1.is_Failure) {
          __E _2_e = _source1.dtor_e;
          unmatched1 = false;
          return Dafny.Helpers.Id<Func<__E, __C>>(_pat_let_tv2)(_2_e);
        }
      }
      if (unmatched1) {
        __T _3_t = _source1.dtor_t;
        unmatched1 = false;
        return Dafny.Helpers.Id<Func<__T, __C>>(_pat_let_tv3)(_3_t);
      }
      throw new System.Exception("unexpected control point");
    }
  }

  public interface _IResult<E, T> {
    bool is_Failure { get; }
    bool is_Success { get; }
    E dtor_e { get; }
    T dtor_t { get; }
    _IResult<__E, __T> DowncastClone<__E, __T>(Func<E, __E> converter0, Func<T, __T> converter1);
  }
  public abstract class Result<E, T> : _IResult<E, T> {
    public Result() {
    }
    public static Common.Data.Result._IResult<E, T> Default(E _default_E) {
      return create_Failure(_default_E);
    }
    public static Dafny.TypeDescriptor<Common.Data.Result._IResult<E, T>> _TypeDescriptor(Dafny.TypeDescriptor<E> _td_E) {
      return new Dafny.TypeDescriptor<Common.Data.Result._IResult<E, T>>(Common.Data.Result.Result<E, T>.Default(_td_E.Default()));
    }
    public static _IResult<E, T> create_Failure(E e) {
      return new Result_Failure<E, T>(e);
    }
    public static _IResult<E, T> create_Success(T t) {
      return new Result_Success<E, T>(t);
    }
    public bool is_Failure { get { return this is Result_Failure<E, T>; } }
    public bool is_Success { get { return this is Result_Success<E, T>; } }
    public E dtor_e {
      get {
        var d = this;
        return ((Result_Failure<E, T>)d)._e;
      }
    }
    public T dtor_t {
      get {
        var d = this;
        return ((Result_Success<E, T>)d)._t;
      }
    }
    public abstract _IResult<__E, __T> DowncastClone<__E, __T>(Func<E, __E> converter0, Func<T, __T> converter1);
  }
  public class Result_Failure<E, T> : Result<E, T> {
    public readonly E _e;
    public Result_Failure(E e) : base() {
      this._e = e;
    }
    public override _IResult<__E, __T> DowncastClone<__E, __T>(Func<E, __E> converter0, Func<T, __T> converter1) {
      if (this is _IResult<__E, __T> dt) { return dt; }
      return new Result_Failure<__E, __T>(converter0(_e));
    }
    public override bool Equals(object other) {
      var oth = other as Common.Data.Result.Result_Failure<E, T>;
      return oth != null && object.Equals(this._e, oth._e);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._e));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Result.Result.Failure";
      s += "(";
      s += Dafny.Helpers.ToString(this._e);
      s += ")";
      return s;
    }
  }
  public class Result_Success<E, T> : Result<E, T> {
    public readonly T _t;
    public Result_Success(T t) : base() {
      this._t = t;
    }
    public override _IResult<__E, __T> DowncastClone<__E, __T>(Func<E, __E> converter0, Func<T, __T> converter1) {
      if (this is _IResult<__E, __T> dt) { return dt; }
      return new Result_Success<__E, __T>(converter1(_t));
    }
    public override bool Equals(object other) {
      var oth = other as Common.Data.Result.Result_Success<E, T>;
      return oth != null && object.Equals(this._t, oth._t);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._t));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Result.Result.Success";
      s += "(";
      s += Dafny.Helpers.ToString(this._t);
      s += ")";
      return s;
    }
  }
} // end of namespace Common.Data.Result
namespace Common.Data.Seq {

  public partial class __default {
    public static BigInteger count<__T>(Dafny.ISequence<Dafny.ISequence<__T>> xs) {
      BigInteger _4___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_4___accumulator);
      } else {
        _4___accumulator = (_4___accumulator) + (new BigInteger(((xs).Select(BigInteger.Zero)).Count));
        Dafny.ISequence<Dafny.ISequence<__T>> _in0 = (xs).Drop(BigInteger.One);
        xs = _in0;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__B> fmap<__A, __B>(Func<__A, __B> f, Dafny.ISequence<__A> xs)
    {
      Dafny.ISequence<__B> _5___accumulator = Dafny.Sequence<__B>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<__B>.Concat(_5___accumulator, Dafny.Sequence<__B>.FromElements());
      } else {
        _5___accumulator = Dafny.Sequence<__B>.Concat(_5___accumulator, Dafny.Sequence<__B>.FromElements(Dafny.Helpers.Id<Func<__A, __B>>(f)((xs).Select(BigInteger.Zero))));
        Func<__A, __B> _in1 = f;
        Dafny.ISequence<__A> _in2 = (xs).Drop(BigInteger.One);
        f = _in1;
        xs = _in2;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__T> intersperse<__T>(Dafny.ISequence<__T> xs, __T c)
    {
      Dafny.ISequence<__T> _6___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_6___accumulator, Dafny.Sequence<__T>.FromElements());
      } else if ((new BigInteger((xs).Count)) == (BigInteger.One)) {
        return Dafny.Sequence<__T>.Concat(_6___accumulator, Dafny.Sequence<__T>.FromElements((xs).Select(BigInteger.Zero)));
      } else {
        _6___accumulator = Dafny.Sequence<__T>.Concat(_6___accumulator, Dafny.Sequence<__T>.FromElements((xs).Select(BigInteger.Zero), c));
        Dafny.ISequence<__T> _in3 = (xs).Drop(BigInteger.One);
        __T _in4 = c;
        xs = _in3;
        c = _in4;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__T> flatten<__T>(Dafny.ISequence<Dafny.ISequence<__T>> xs) {
      Dafny.ISequence<__T> _7___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_7___accumulator, Dafny.Sequence<__T>.FromElements());
      } else {
        _7___accumulator = Dafny.Sequence<__T>.Concat(_7___accumulator, (xs).Select(BigInteger.Zero));
        Dafny.ISequence<Dafny.ISequence<__T>> _in5 = (xs).Drop(BigInteger.One);
        xs = _in5;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.ISequence<__T>> splitOnHelp<__T>(Dafny.ISequence<__T> xs, Dafny.ISequence<__T> x, Dafny.ISequence<__T> heap)
    {
      Dafny.ISequence<Dafny.ISequence<__T>> _8___accumulator = Dafny.Sequence<Dafny.ISequence<__T>>.FromElements();
    TAIL_CALL_START: ;
      if ((xs).Equals(Dafny.Sequence<__T>.FromElements())) {
        return Dafny.Sequence<Dafny.ISequence<__T>>.Concat(_8___accumulator, Dafny.Sequence<Dafny.ISequence<__T>>.FromElements(heap));
      } else if ((x).Contains((xs).Select(BigInteger.Zero))) {
        _8___accumulator = Dafny.Sequence<Dafny.ISequence<__T>>.Concat(_8___accumulator, Dafny.Sequence<Dafny.ISequence<__T>>.FromElements(heap));
        Dafny.ISequence<__T> _in6 = (xs).Drop(BigInteger.One);
        Dafny.ISequence<__T> _in7 = x;
        Dafny.ISequence<__T> _in8 = Dafny.Sequence<__T>.FromElements();
        xs = _in6;
        x = _in7;
        heap = _in8;
        goto TAIL_CALL_START;
      } else {
        Dafny.ISequence<__T> _in9 = (xs).Drop(BigInteger.One);
        Dafny.ISequence<__T> _in10 = x;
        Dafny.ISequence<__T> _in11 = Dafny.Sequence<__T>.Concat(heap, Dafny.Sequence<__T>.FromElements((xs).Select(BigInteger.Zero)));
        xs = _in9;
        x = _in10;
        heap = _in11;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.ISequence<__T>> splitOn<__T>(Dafny.ISequence<__T> xs, Dafny.ISequence<__T> x)
    {
      return Common.Data.Seq.__default.splitOnHelp<__T>(xs, x, Dafny.Sequence<__T>.FromElements());
    }
    public static Dafny.ISequence<__T> replicate<__T>(BigInteger cnt, __T c)
    {
      Dafny.ISequence<__T> _9___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((cnt).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_9___accumulator, Dafny.Sequence<__T>.FromElements());
      } else {
        _9___accumulator = Dafny.Sequence<__T>.Concat(_9___accumulator, Dafny.Sequence<__T>.FromElements(c));
        BigInteger _in12 = (cnt) - (BigInteger.One);
        __T _in13 = c;
        cnt = _in12;
        c = _in13;
        goto TAIL_CALL_START;
      }
    }
    public static Common.Data.Maybe._IMaybe<__T> head<__T>(Dafny.ISequence<__T> xs) {
      if ((xs).Equals(Dafny.Sequence<__T>.FromElements())) {
        return Common.Data.Maybe.Maybe<__T>.create_Nothing();
      } else {
        return Common.Data.Maybe.Maybe<__T>.create_Just((xs).Select(BigInteger.Zero));
      }
    }
    public static Common.Data.Maybe._IMaybe<Dafny.ISequence<__T>> tail<__T>(Dafny.ISequence<__T> xs) {
      if ((xs).Equals(Dafny.Sequence<__T>.FromElements())) {
        return Common.Data.Maybe.Maybe<Dafny.ISequence<__T>>.create_Nothing();
      } else {
        return Common.Data.Maybe.Maybe<Dafny.ISequence<__T>>.create_Just((xs).Drop(BigInteger.One));
      }
    }
    public static Common.Data.Maybe._IMaybe<_System._ITuple2<__T, Dafny.ISequence<__T>>> splitCons<__T>(Dafny.ISequence<__T> xs) {
      if ((xs).Equals(Dafny.Sequence<__T>.FromElements())) {
        return Common.Data.Maybe.Maybe<_System._ITuple2<__T, Dafny.ISequence<__T>>>.create_Nothing();
      } else {
        return Common.Data.Maybe.Maybe<_System._ITuple2<__T, Dafny.ISequence<__T>>>.create_Just(_System.Tuple2<__T, Dafny.ISequence<__T>>.create((xs).Select(BigInteger.Zero), (xs).Drop(BigInteger.One)));
      }
    }
    public static Common.Data.Maybe._IMaybe<__T> singleton<__T>(Dafny.ISequence<__T> xs) {
      if ((xs).Equals(Dafny.Sequence<__T>.FromElements())) {
        return Common.Data.Maybe.Maybe<__T>.create_Nothing();
      } else if ((new BigInteger((xs).Count)) > (BigInteger.One)) {
        return Common.Data.Maybe.Maybe<__T>.create_Nothing();
      } else {
        return Common.Data.Maybe.Maybe<__T>.create_Just((xs).Select(BigInteger.Zero));
      }
    }
  }
} // end of namespace Common.Data.Seq
namespace Common.Data.String {

  public partial class __default {
    public static Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> splitOn(Dafny.ISequence<Dafny.Rune> str, Dafny.ISequence<Dafny.Rune> cs)
    {
      return Common.Data.Seq.__default.splitOn<Dafny.Rune>(str, cs);
    }
    public static Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> words(Dafny.ISequence<Dafny.Rune> s) {
      return Common.Data.String.__default.splitOn(s, Dafny.Sequence<Dafny.Rune>.FromElements(new Dafny.Rune(' ')));
    }
    public static Dafny.ISequence<Dafny.Rune> wordsUn(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> ws) {
      return Common.Data.Seq.__default.flatten<Dafny.Rune>(Common.Data.Seq.__default.intersperse<Dafny.ISequence<Dafny.Rune>>(ws, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")));
    }
    public static Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> lines(Dafny.ISequence<Dafny.Rune> s) {
      return Common.Data.String.__default.splitOn(s, Dafny.Sequence<Dafny.Rune>.FromElements(new Dafny.Rune('\n'), new Dafny.Rune('\r')));
    }
    public static Dafny.ISequence<Dafny.Rune> linesUn(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> ws) {
      return Common.Data.Seq.__default.flatten<Dafny.Rune>(Common.Data.Seq.__default.intersperse<Dafny.ISequence<Dafny.Rune>>(ws, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")));
    }
  }
} // end of namespace Common.Data.String
namespace Common.Data.Nat {

  public partial class __default {
    public static Common.Data.Maybe._IMaybe<BigInteger> digitFromChar(Dafny.Rune c) {
      Dafny.Rune _source2 = c;
      bool unmatched2 = true;
      if (unmatched2) {
        if ((_source2) == (new Dafny.Rune('0'))) {
          unmatched2 = false;
          return Common.Data.Maybe.Maybe<BigInteger>.create_Just(BigInteger.Zero);
        }
      }
      if (unmatched2) {
        if ((_source2) == (new Dafny.Rune('1'))) {
          unmatched2 = false;
          return Common.Data.Maybe.Maybe<BigInteger>.create_Just(BigInteger.One);
        }
      }
      if (unmatched2) {
        if ((_source2) == (new Dafny.Rune('2'))) {
          unmatched2 = false;
          return Common.Data.Maybe.Maybe<BigInteger>.create_Just(new BigInteger(2));
        }
      }
      if (unmatched2) {
        if ((_source2) == (new Dafny.Rune('3'))) {
          unmatched2 = false;
          return Common.Data.Maybe.Maybe<BigInteger>.create_Just(new BigInteger(3));
        }
      }
      if (unmatched2) {
        if ((_source2) == (new Dafny.Rune('4'))) {
          unmatched2 = false;
          return Common.Data.Maybe.Maybe<BigInteger>.create_Just(new BigInteger(4));
        }
      }
      if (unmatched2) {
        if ((_source2) == (new Dafny.Rune('5'))) {
          unmatched2 = false;
          return Common.Data.Maybe.Maybe<BigInteger>.create_Just(new BigInteger(5));
        }
      }
      if (unmatched2) {
        if ((_source2) == (new Dafny.Rune('6'))) {
          unmatched2 = false;
          return Common.Data.Maybe.Maybe<BigInteger>.create_Just(new BigInteger(6));
        }
      }
      if (unmatched2) {
        if ((_source2) == (new Dafny.Rune('7'))) {
          unmatched2 = false;
          return Common.Data.Maybe.Maybe<BigInteger>.create_Just(new BigInteger(7));
        }
      }
      if (unmatched2) {
        if ((_source2) == (new Dafny.Rune('8'))) {
          unmatched2 = false;
          return Common.Data.Maybe.Maybe<BigInteger>.create_Just(new BigInteger(8));
        }
      }
      if (unmatched2) {
        if ((_source2) == (new Dafny.Rune('9'))) {
          unmatched2 = false;
          return Common.Data.Maybe.Maybe<BigInteger>.create_Just(new BigInteger(9));
        }
      }
      if (unmatched2) {
        Dafny.Rune _10_x = _source2;
        unmatched2 = false;
        return Common.Data.Maybe.Maybe<BigInteger>.create_Nothing();
      }
      throw new System.Exception("unexpected control point");
    }
    public static Common.Data.Maybe._IMaybe<Dafny.ISequence<BigInteger>> digitsFromString(Dafny.ISequence<Dafny.Rune> s) {
      if ((s).Equals(Dafny.Sequence<Dafny.Rune>.FromElements())) {
        return Common.Data.Maybe.Maybe<Dafny.ISequence<BigInteger>>.create_Just(Dafny.Sequence<BigInteger>.FromElements());
      } else {
        return Common.Data.Maybe.__default.maybe<BigInteger, Common.Data.Maybe._IMaybe<Dafny.ISequence<BigInteger>>>(Common.Data.Nat.__default.digitFromChar((s).Select(BigInteger.Zero)), Common.Data.Maybe.Maybe<Dafny.ISequence<BigInteger>>.create_Nothing(), Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<BigInteger, Common.Data.Maybe._IMaybe<Dafny.ISequence<BigInteger>>>>>((_11_s) => ((System.Func<BigInteger, Common.Data.Maybe._IMaybe<Dafny.ISequence<BigInteger>>>)((_12_c) => {
          return Common.Data.Maybe.__default.maybe<Dafny.ISequence<BigInteger>, Common.Data.Maybe._IMaybe<Dafny.ISequence<BigInteger>>>(Common.Data.Nat.__default.digitsFromString((_11_s).Drop(BigInteger.One)), Common.Data.Maybe.Maybe<Dafny.ISequence<BigInteger>>.create_Nothing(), Dafny.Helpers.Id<Func<BigInteger, Func<Dafny.ISequence<BigInteger>, Common.Data.Maybe._IMaybe<Dafny.ISequence<BigInteger>>>>>((_13_c) => ((System.Func<Dafny.ISequence<BigInteger>, Common.Data.Maybe._IMaybe<Dafny.ISequence<BigInteger>>>)((_14_cs) => {
            return Common.Data.Maybe.Maybe<Dafny.ISequence<BigInteger>>.create_Just(Dafny.Sequence<BigInteger>.Concat(Dafny.Sequence<BigInteger>.FromElements(_13_c), _14_cs));
          })))(_12_c));
        })))(s));
      }
    }
  }
} // end of namespace Common.Data.Nat
namespace Common.Data {

} // end of namespace Common.Data
namespace Common {

} // end of namespace Common
namespace Commands {

  public partial class __default {
    public static Common.Data.Maybe._IMaybe<Commands._ICMD> processQuit(Dafny.ISequence<Dafny.Rune> cmd, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> args)
    {
      if ((cmd).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("quit"))) {
        return Common.Data.Maybe.Maybe<Commands._ICMD>.create_Just(Commands.CMD.create_Quit());
      } else {
        return Common.Data.Maybe.Maybe<Commands._ICMD>.create_Nothing();
      }
    }
    public static Common.Data.Maybe._IMaybe<Commands._ICMD> processHelp(Dafny.ISequence<Dafny.Rune> cmd, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> args)
    {
      if ((((cmd).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("help"))) || ((cmd).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("h")))) || ((cmd).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("?")))) {
        return Common.Data.Maybe.Maybe<Commands._ICMD>.create_Just(Commands.CMD.create_Help());
      } else {
        return Common.Data.Maybe.Maybe<Commands._ICMD>.create_Nothing();
      }
    }
    public static Common.Data.Maybe._IMaybe<__T> whenNothing<__T>(Common.Data.Maybe._IMaybe<__T> m, Common.Data.Maybe._IMaybe<__T> alt)
    {
      if (!object.Equals(m, Common.Data.Maybe.Maybe<__T>.create_Nothing())) {
        return m;
      } else {
        return alt;
      }
    }
    public static Common.Data.Maybe._IMaybe<Commands._ICMD> process(Dafny.ISequence<Dafny.Rune> cmd, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> args)
    {
      return Commands.__default.whenNothing<Commands._ICMD>(Commands.__default.processQuit(cmd, args), Commands.__default.processHelp(cmd, args));
    }
    public static BigInteger stringToNat(Dafny.ISequence<Dafny.Rune> s) {
      if ((s).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"))) {
        return BigInteger.Zero;
      } else if ((s).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("1"))) {
        return BigInteger.One;
      } else if ((s).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("2"))) {
        return new BigInteger(2);
      } else if ((s).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("3"))) {
        return new BigInteger(3);
      } else if ((s).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("4"))) {
        return new BigInteger(4);
      } else if ((s).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("5"))) {
        return new BigInteger(5);
      } else if ((s).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("6"))) {
        return new BigInteger(6);
      } else if ((s).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("7"))) {
        return new BigInteger(7);
      } else if ((s).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("8"))) {
        return new BigInteger(8);
      } else if ((s).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("9"))) {
        return new BigInteger(9);
      } else {
        return BigInteger.Zero;
      }
    }
    public static Common.Data.Maybe._IMaybe<Dafny.ISequence<Dafny.Rune>> stripColon(Dafny.ISequence<Dafny.Rune> s) {
      if (((new BigInteger((s).Count)).Sign == 1) && (((s).Select(BigInteger.Zero)) == (new Dafny.Rune(':')))) {
        return Common.Data.Maybe.Maybe<Dafny.ISequence<Dafny.Rune>>.create_Just((s).Drop(BigInteger.One));
      } else {
        return Common.Data.Maybe.Maybe<Dafny.ISequence<Dafny.Rune>>.create_Nothing();
      }
    }
    public static bool isWhitespace(Dafny.Rune c) {
      return (c) == (new Dafny.Rune(' '));
    }
    public static Dafny.ISequence<Dafny.Rune> dropLeadingSpaces(Dafny.ISequence<Dafny.Rune> s) {
    TAIL_CALL_START: ;
      if ((s).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      } else if (Commands.__default.isWhitespace((s).Select(BigInteger.Zero))) {
        Dafny.ISequence<Dafny.Rune> _in14 = (s).Drop(BigInteger.One);
        s = _in14;
        goto TAIL_CALL_START;
      } else {
        return s;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> takeWord(Dafny.ISequence<Dafny.Rune> s) {
      Dafny.ISequence<Dafny.Rune> _15___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if (((s).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) || (Commands.__default.isWhitespace((s).Select(BigInteger.Zero)))) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_15___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else {
        _15___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_15___accumulator, (s).Subsequence(BigInteger.Zero, BigInteger.One));
        Dafny.ISequence<Dafny.Rune> _in15 = (s).Drop(BigInteger.One);
        s = _in15;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> words(Dafny.ISequence<Dafny.Rune> s) {
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _16___accumulator = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
    TAIL_CALL_START: ;
      Dafny.ISequence<Dafny.Rune> _17_s_k = Commands.__default.dropLeadingSpaces(s);
      if ((_17_s_k).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
        return Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_16___accumulator, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
      } else {
        Dafny.ISequence<Dafny.Rune> _18_w = Commands.__default.takeWord(_17_s_k);
        _16___accumulator = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_16___accumulator, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_18_w));
        Dafny.ISequence<Dafny.Rune> _in16 = (_17_s_k).Drop(new BigInteger((_18_w).Count));
        s = _in16;
        goto TAIL_CALL_START;
      }
    }
    public static Common.Data.Maybe._IMaybe<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>> splitCons(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> ws) {
      if ((new BigInteger((ws).Count)).Sign == 1) {
        return Common.Data.Maybe.Maybe<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>>.create_Just(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create((ws).Select(BigInteger.Zero), (ws).Drop(BigInteger.One)));
      } else {
        return Common.Data.Maybe.Maybe<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>>.create_Nothing();
      }
    }
    public static Common.Data.Maybe._IMaybe<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>> preprocess(Dafny.ISequence<Dafny.Rune> s) {
      return Common.Data.Maybe.__default.maybe<Dafny.ISequence<Dafny.Rune>, Common.Data.Maybe._IMaybe<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>>>(Commands.__default.stripColon(s), Common.Data.Maybe.Maybe<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>>.create_Nothing(), ((System.Func<Dafny.ISequence<Dafny.Rune>, Common.Data.Maybe._IMaybe<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>>>)((_19_res) => {
        return Commands.__default.splitCons(Commands.__default.words(_19_res));
      })));
    }
    public static Common.Data.Maybe._IMaybe<Commands._ICMD> fromString(Dafny.ISequence<Dafny.Rune> s) {
      return Common.Data.Maybe.__default.maybe<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>, Common.Data.Maybe._IMaybe<Commands._ICMD>>(Commands.__default.preprocess(s), Common.Data.Maybe.Maybe<Commands._ICMD>.create_Nothing(), ((System.Func<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>, Common.Data.Maybe._IMaybe<Commands._ICMD>>)((_20_pair) => {
        return ((!object.Equals(Commands.__default.process((_20_pair).dtor__0, (_20_pair).dtor__1), Common.Data.Maybe.Maybe<Commands._ICMD>.create_Nothing())) ? (Commands.__default.process((_20_pair).dtor__0, (_20_pair).dtor__1)) : (((((_20_pair).dtor__0).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("stop"))) ? (Common.Data.Maybe.Maybe<Commands._ICMD>.create_Just(Commands.CMD.create_Stop())) : ((((((_20_pair).dtor__0).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("play"))) && ((new BigInteger(((_20_pair).dtor__1).Count)) == (new BigInteger(2)))) ? (Common.Data.Maybe.Maybe<Commands._ICMD>.create_Just(Commands.CMD.create_Play(Commands.__default.stringToNat(((_20_pair).dtor__1).Select(BigInteger.Zero)), ((_20_pair).dtor__1).Select(BigInteger.One)))) : ((((((_20_pair).dtor__0).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("guess"))) && ((new BigInteger(((_20_pair).dtor__1).Count)) == (BigInteger.One))) ? (Common.Data.Maybe.Maybe<Commands._ICMD>.create_Just(Commands.CMD.create_Guess(((_20_pair).dtor__1).Select(BigInteger.Zero)))) : (Common.Data.Maybe.Maybe<Commands._ICMD>.create_Nothing()))))))));
      })));
    }
  }

  public interface _ICMD {
    bool is_Quit { get; }
    bool is_Help { get; }
    bool is_Play { get; }
    bool is_Guess { get; }
    bool is_Stop { get; }
    BigInteger dtor_n { get; }
    Dafny.ISequence<Dafny.Rune> dtor_secret { get; }
    Dafny.ISequence<Dafny.Rune> dtor_guess { get; }
    _ICMD DowncastClone();
  }
  public abstract class CMD : _ICMD {
    public CMD() {
    }
    private static readonly Commands._ICMD theDefault = create_Quit();
    public static Commands._ICMD Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Commands._ICMD> _TYPE = new Dafny.TypeDescriptor<Commands._ICMD>(Commands.CMD.Default());
    public static Dafny.TypeDescriptor<Commands._ICMD> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICMD create_Quit() {
      return new CMD_Quit();
    }
    public static _ICMD create_Help() {
      return new CMD_Help();
    }
    public static _ICMD create_Play(BigInteger n, Dafny.ISequence<Dafny.Rune> secret) {
      return new CMD_Play(n, secret);
    }
    public static _ICMD create_Guess(Dafny.ISequence<Dafny.Rune> guess) {
      return new CMD_Guess(guess);
    }
    public static _ICMD create_Stop() {
      return new CMD_Stop();
    }
    public bool is_Quit { get { return this is CMD_Quit; } }
    public bool is_Help { get { return this is CMD_Help; } }
    public bool is_Play { get { return this is CMD_Play; } }
    public bool is_Guess { get { return this is CMD_Guess; } }
    public bool is_Stop { get { return this is CMD_Stop; } }
    public BigInteger dtor_n {
      get {
        var d = this;
        return ((CMD_Play)d)._n;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_secret {
      get {
        var d = this;
        return ((CMD_Play)d)._secret;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_guess {
      get {
        var d = this;
        return ((CMD_Guess)d)._guess;
      }
    }
    public abstract _ICMD DowncastClone();
  }
  public class CMD_Quit : CMD {
    public CMD_Quit() : base() {
    }
    public override _ICMD DowncastClone() {
      if (this is _ICMD dt) { return dt; }
      return new CMD_Quit();
    }
    public override bool Equals(object other) {
      var oth = other as Commands.CMD_Quit;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Commands.CMD.Quit";
      return s;
    }
  }
  public class CMD_Help : CMD {
    public CMD_Help() : base() {
    }
    public override _ICMD DowncastClone() {
      if (this is _ICMD dt) { return dt; }
      return new CMD_Help();
    }
    public override bool Equals(object other) {
      var oth = other as Commands.CMD_Help;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Commands.CMD.Help";
      return s;
    }
  }
  public class CMD_Play : CMD {
    public readonly BigInteger _n;
    public readonly Dafny.ISequence<Dafny.Rune> _secret;
    public CMD_Play(BigInteger n, Dafny.ISequence<Dafny.Rune> secret) : base() {
      this._n = n;
      this._secret = secret;
    }
    public override _ICMD DowncastClone() {
      if (this is _ICMD dt) { return dt; }
      return new CMD_Play(_n, _secret);
    }
    public override bool Equals(object other) {
      var oth = other as Commands.CMD_Play;
      return oth != null && this._n == oth._n && object.Equals(this._secret, oth._secret);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._n));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._secret));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Commands.CMD.Play";
      s += "(";
      s += Dafny.Helpers.ToString(this._n);
      s += ", ";
      s += this._secret.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class CMD_Guess : CMD {
    public readonly Dafny.ISequence<Dafny.Rune> _guess;
    public CMD_Guess(Dafny.ISequence<Dafny.Rune> guess) : base() {
      this._guess = guess;
    }
    public override _ICMD DowncastClone() {
      if (this is _ICMD dt) { return dt; }
      return new CMD_Guess(_guess);
    }
    public override bool Equals(object other) {
      var oth = other as Commands.CMD_Guess;
      return oth != null && object.Equals(this._guess, oth._guess);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._guess));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Commands.CMD.Guess";
      s += "(";
      s += this._guess.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class CMD_Stop : CMD {
    public CMD_Stop() : base() {
    }
    public override _ICMD DowncastClone() {
      if (this is _ICMD dt) { return dt; }
      return new CMD_Stop();
    }
    public override bool Equals(object other) {
      var oth = other as Commands.CMD_Stop;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Commands.CMD.Stop";
      return s;
    }
  }
} // end of namespace Commands
namespace ConsoleIO {

} // end of namespace ConsoleIO
namespace CS886 {

  public partial class __default {
    public static void _Main(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> __noArgsParameter)
    {
      CS886.__default.REPL(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
    }
    public static void REPL(Dafny.ISequence<Dafny.Rune> prompt)
    {
      bool _21_inGame;
      _21_inGame = false;
      Dafny.ISequence<Dafny.Rune> _22_secret;
      _22_secret = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      BigInteger _23_remainingTries;
      _23_remainingTries = BigInteger.Zero;
      while (true) {
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.Concat(prompt, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "))).ToVerbatimString(false));
        Dafny.ISequence<Dafny.Rune> _24_resp;
        Dafny.ISequence<Dafny.Rune> _out0;
        _out0 = ConsoleIO.__default.INTERNAL__ReadLine();
        _24_resp = _out0;
        Common.Data.Maybe._IMaybe<Commands._ICMD> _25_cmdOpt;
        _25_cmdOpt = Commands.__default.fromString(_24_resp);
        Common.Data.Maybe._IMaybe<Commands._ICMD> _source3 = _25_cmdOpt;
        bool unmatched3 = true;
        if (unmatched3) {
          if (_source3.is_Nothing) {
            unmatched3 = false;
            {
              Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Invalid command.\n")).ToVerbatimString(false));
              goto continue_0;
            }
          }
        }
        if (unmatched3) {
          Commands._ICMD _26_cmd = _source3.dtor_t;
          unmatched3 = false;
          Commands._ICMD _source4 = _26_cmd;
          bool unmatched4 = true;
          if (unmatched4) {
            if (_source4.is_Quit) {
              unmatched4 = false;
              {
                if (_21_inGame) {
                  Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Abandoning game, goodbye\n")).ToVerbatimString(false));
                } else {
                  Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Exiting game\n")).ToVerbatimString(false));
                }
                goto after_0;
              }
            }
          }
          if (unmatched4) {
            if (_source4.is_Help) {
              unmatched4 = false;
              {
                Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Yays & Naes\n\n")).ToVerbatimString(false));
                Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Commands:\n\n")).ToVerbatimString(false));
                Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(":quit         -- Exit programme\n")).ToVerbatimString(false));
                Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(":play [n] [s] -- Play a game with n tries and a secret sequence s\n")).ToVerbatimString(false));
                Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(":guess [seq]  -- guess the secret\n")).ToVerbatimString(false));
                Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(":stop         -- end game\n")).ToVerbatimString(false));
                goto continue_0;
              }
            }
          }
          if (unmatched4) {
            if (_source4.is_Play) {
              BigInteger _27_n = _source4.dtor_n;
              Dafny.ISequence<Dafny.Rune> _28_s = _source4.dtor_secret;
              unmatched4 = false;
              {
                if (_21_inGame) {
                  if ((_24_resp).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(":play 4 1234"))) {
                    Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Already in a game.\n")).ToVerbatimString(false));
                  } else {
                    Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Invalid command.\n")).ToVerbatimString(false));
                  }
                } else {
                  if (((_27_n) < (new BigInteger(4))) || (CS886.__default.hasDuplicates(_28_s))) {
                    Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Invalid command.\n")).ToVerbatimString(false));
                  } else if ((new BigInteger((_28_s).Count)) < (new BigInteger(4))) {
                    Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("The secret is too short.\n")).ToVerbatimString(false));
                  } else {
                    _21_inGame = true;
                    _23_remainingTries = _27_n;
                    _22_secret = _28_s;
                    Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Game on!\n")).ToVerbatimString(false));
                  }
                }
                goto continue_0;
              }
            }
          }
          if (unmatched4) {
            if (_source4.is_Guess) {
              Dafny.ISequence<Dafny.Rune> _29_g = _source4.dtor_guess;
              unmatched4 = false;
              {
                if (!(_21_inGame)) {
                  Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Not in a game.\n")).ToVerbatimString(false));
                } else if ((new BigInteger((_29_g).Count)) != (new BigInteger((_22_secret).Count))) {
                  Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Invalid command.\n")).ToVerbatimString(false));
                } else {
                  if ((_29_g).Equals(_22_secret)) {
                    Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Congratulations you guessed correctly!\n")).ToVerbatimString(false));
                    _21_inGame = false;
                  } else {
                    BigInteger _30_yays;
                    _30_yays = CS886.__default.countYays(_22_secret, _29_g);
                    BigInteger _31_naes;
                    _31_naes = CS886.__default.countNaes(_22_secret, _29_g);
                    Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.Concat(CS886.__default.formatSecret(_29_g), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "))).ToVerbatimString(false));
                    Dafny.Helpers.Print((_30_yays));
                    Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" yay ")).ToVerbatimString(false));
                    Dafny.Helpers.Print((_31_naes));
                    Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" nae\n")).ToVerbatimString(false));
                    if ((_23_remainingTries).Sign == 1) {
                      _23_remainingTries = (_23_remainingTries) - (BigInteger.One);
                    }
                    if ((_23_remainingTries).Sign == 0) {
                      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("No more turns left!\n")).ToVerbatimString(false));
                      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("The secret was: \n"), _22_secret), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"))).ToVerbatimString(false));
                      _21_inGame = false;
                    }
                  }
                }
                goto continue_0;
              }
            }
          }
          if (unmatched4) {
            unmatched4 = false;
            {
              if (!(_21_inGame)) {
                Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Not in a game.\n")).ToVerbatimString(false));
              } else {
                _21_inGame = false;
                Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Abandoning game, resetting state.\n")).ToVerbatimString(false));
              }
              goto continue_0;
            }
          }
        }
      continue_0: ;
      }
    after_0: ;
    }
    public static bool hasDuplicates(Dafny.ISequence<Dafny.Rune> s) {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, bool>>((_32_s) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((_32_s).Count)), false, (((_exists_var_0) => {
        BigInteger _33_i = (BigInteger)_exists_var_0;
        return Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange((_33_i) + (BigInteger.One), new BigInteger((_32_s).Count)), false, (((_exists_var_1) => {
          BigInteger _34_j = (BigInteger)_exists_var_1;
          return ((((_33_i).Sign != -1) && ((_33_i) < (_34_j))) && ((_34_j) < (new BigInteger((_32_s).Count)))) && (((_32_s).Select(_33_i)) == ((_32_s).Select(_34_j)));
        })));
      }))))(s);
    }
    public static Dafny.Rune firstDuplicate(Dafny.ISequence<Dafny.Rune> s) {
      return (s).Select(BigInteger.Zero);
    }
    public static bool contains(Dafny.ISequence<Dafny.Rune> s, Dafny.Rune c)
    {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Dafny.Rune, bool>>((_35_s, _36_c) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((_35_s).Count)), false, (((_exists_var_2) => {
        BigInteger _37_i = (BigInteger)_exists_var_2;
        return (((_37_i).Sign != -1) && ((_37_i) < (new BigInteger((_35_s).Count)))) && (((_35_s).Select(_37_i)) == (_36_c));
      }))))(s, c);
    }
    public static BigInteger countYays(Dafny.ISequence<Dafny.Rune> secret, Dafny.ISequence<Dafny.Rune> guess)
    {
      BigInteger _38___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((secret).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_38___accumulator);
      } else {
        _38___accumulator = (_38___accumulator) + (((((secret).Select(BigInteger.Zero)) == ((guess).Select(BigInteger.Zero))) ? (BigInteger.One) : (BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in17 = (secret).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.Rune> _in18 = (guess).Drop(BigInteger.One);
        secret = _in17;
        guess = _in18;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger countCommon(Dafny.ISequence<Dafny.Rune> secret, Dafny.ISequence<Dafny.Rune> guess)
    {
      BigInteger _39___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((guess).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
        return (BigInteger.Zero) + (_39___accumulator);
      } else {
        _39___accumulator = (_39___accumulator) + (((CS886.__default.contains(secret, (guess).Select(BigInteger.Zero))) ? (BigInteger.One) : (BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in19 = secret;
        Dafny.ISequence<Dafny.Rune> _in20 = (guess).Drop(BigInteger.One);
        secret = _in19;
        guess = _in20;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger countNaes(Dafny.ISequence<Dafny.Rune> secret, Dafny.ISequence<Dafny.Rune> guess)
    {
      BigInteger _40_common = CS886.__default.countCommon(secret, guess);
      BigInteger _41_yays = CS886.__default.countYays(secret, guess);
      if ((_40_common) >= (_41_yays)) {
        return (_40_common) - (_41_yays);
      } else {
        return BigInteger.Zero;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> formatSecret(Dafny.ISequence<Dafny.Rune> s) {
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[]");
      } else {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("["), (s).Subsequence(BigInteger.Zero, BigInteger.One)), CS886.__default.formatSecretRec(s, BigInteger.One)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
      }
    }
    public static Dafny.ISequence<Dafny.Rune> formatSecretRec(Dafny.ISequence<Dafny.Rune> s, BigInteger i)
    {
      Dafny.ISequence<Dafny.Rune> _42___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((i) >= (new BigInteger((s).Count))) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_42___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else {
        _42___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_42___accumulator, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "), (s).Subsequence(i, (i) + (BigInteger.One))));
        Dafny.ISequence<Dafny.Rune> _in21 = s;
        BigInteger _in22 = (i) + (BigInteger.One);
        s = _in21;
        i = _in22;
        goto TAIL_CALL_START;
      }
    }
  }
} // end of namespace CS886
namespace _module {

} // end of namespace _module
class __CallToMain {
  public static void Main(string[] args) {
    Dafny.Helpers.WithHaltHandling(() => CS886.__default._Main(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.UnicodeFromMainArguments(args)));
  }
}
