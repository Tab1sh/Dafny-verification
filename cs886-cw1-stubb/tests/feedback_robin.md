start-stop/001-help: only issue i can see is that instead of escaping letters like 'n' and 's' as expected, you just print n and s
Expected: Play a game with `n` tries and a secret sequence `s`
Actual: Play a game with n tries and a secret sequence s


game-bad/002-exhaust:
Expected:
> No more turns left!
The secret was:
[1, 2, 3, 4]
> Abandoning game, goodbye.

Yours:
No more turns left!
The secret was:
1234
> Not in a game.
> Exiting game

Few issues, you are not printing the secret as a list. You somehow have an extra Not in game error, which indicates quitting is not handled properly.


game-bad/001-malformed:
There are some invalid commands you are not handling. Look at the input for the test and run your game manually and debug to see which command you are not handling. I assume its a command which is SUPPOSED to be invalid, but maybe its being parsed as Nothing.

game-bad/000-easy:
- Some invalid command is not being parsed correctly, look at the test input to see what command is not being handled properly
- Secret is not printed as array
- Your exit state seems to be wrong. It shouldnt be saying not in game, just the quitting the game message.
