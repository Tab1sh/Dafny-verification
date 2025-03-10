include "Common.dfy"

module Commands {
  import opened Common.Data.Maybe
  import opened Common.Data.Seq
  import opened Common.Data.String
  import opened Common.Data.Nat

  // Datatype representing the possible commands.
  datatype CMD =
    Quit |                        // Quit the application.
    Help |                        // Display help information.
    Play(n: nat, secret: string) | // Start a game with n tries and a secret.
    Guess(guess: string) |         // Make a guess.
    Stop                          // Stop the current game.

  // processQuit: Returns Just(Quit) if the command word is "quit"; otherwise, Nothing.
  function processQuit(cmd: string, args: seq<string>): Maybe<CMD> {
    if cmd == "quit" then Maybe.Just(Quit) else Maybe.Nothing
  }

  // processHelp: Returns Just(Help) if the command word is "help", "h", or "?"; otherwise, Nothing.
  function processHelp(cmd: string, args: seq<string>): Maybe<CMD> {
    if cmd == "help" || cmd == "h" || cmd == "?" then Maybe.Just(Help) else Maybe.Nothing
  }

  // whenNothing: Returns m if it is not Nothing; otherwise, returns alt.
  function whenNothing<T>(m: Maybe<T>, alt: Maybe<T>) : Maybe<T> {
    if m != Maybe.Nothing then m else alt
  }

  // process: Combines processQuit and processHelp.
  // It returns the result of processQuit(cmd, args) if not Nothing;
  // otherwise, returns processHelp(cmd, args).
  function process(cmd: string, args: seq<string>) : Maybe<CMD> {
    whenNothing(processQuit(cmd, args), processHelp(cmd, args))
  }

  // stringToNat: Converts a one-digit string to a natural number.
  function stringToNat(s: string): nat {
    if s == "0" then 0
    else if s == "1" then 1
    else if s == "2" then 2
    else if s == "3" then 3
    else if s == "4" then 4
    else if s == "5" then 5
    else if s == "6" then 6
    else if s == "7" then 7
    else if s == "8" then 8
    else if s == "9" then 9
    else 0
  }

  // stripColon: Removes the leading colon from the input string.
  function stripColon(s: string): Maybe<string> {
    if |s| > 0 && s[0] == ':' then Maybe.Just(s[1..]) else Maybe.Nothing
  }

  // isWhitespace: Checks if a character is a whitespace (here, the space character).
  function isWhitespace(c: char): bool {
    c == ' '
  }

  // dropLeadingSpaces: Recursively removes leading spaces from a string.
  function dropLeadingSpaces(s: string): string {
    if s == "" then ""
    else if isWhitespace(s[0]) then dropLeadingSpaces(s[1..]) else s
  }

  // takeWord: Extracts a word from the beginning of a string (stops at the first whitespace).
  function takeWord(s: string): string {
    if s == "" || isWhitespace(s[0]) then ""
    else s[0..1] + takeWord(s[1..])
  }

  // words: Splits a string into a sequence of words.
  function words(s: string): seq<string> {
    var s' := dropLeadingSpaces(s);
    if s' == "" then []
    else
      var w := takeWord(s');
      [w] + words(s'[|w|..])
  }

  // splitCons: Separates a non-empty sequence of words into a tuple (command, arguments).
  function splitCons(ws: seq<string>): Maybe<(string, seq<string>)> {
    if |ws| > 0 then Maybe.Just((ws[0], ws[1..])) else Maybe.Nothing
  }

  // preprocess: Processes an input command string by:
  //   1. Removing the leading colon,
  //   2. Splitting the remainder into words,
  //   3. Separating the command (first word) from its arguments.
  function preprocess(s: string): Maybe<(string, seq<string>)> {
    maybe(stripColon(s), Maybe.Nothing, (res: string) => splitCons(words(res)))
  }

  // fromString: Parses an input string into a CMD.
  // It pre-processes the input to obtain (command, arguments) then:
  //   - Uses process (combining quit and help) to handle those commands.
  //   - Otherwise, checks for "stop", "play", or "guess" commands.
  function fromString(s: string): Maybe<CMD> {
    maybe(preprocess(s), Maybe.Nothing, (pair: (string, seq<string>)) =>
      if process(pair.0, pair.1) != Maybe.Nothing then process(pair.0, pair.1)
      else if pair.0 == "stop" then
        Maybe.Just(Stop)
      else if pair.0 == "play" && |pair.1| == 2 then
        Maybe.Just(Play(stringToNat(pair.1[0]), pair.1[1]))
      else if pair.0 == "guess" && |pair.1| == 1 then
        Maybe.Just(Guess(pair.1[0]))
      else
        Maybe.Nothing
    )
  }
}