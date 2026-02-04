package utwente.module2.quarto.server;

import utwente.module2.quarto.gamelogic.*;
import utwente.module2.quarto.gamelogic.player.HumanPlayer;
import utwente.module2.quarto.gamelogic.player.Player;
import utwente.module2.quarto.networking.Packet;
import utwente.module2.quarto.networking.Protocol;

/**
 * Manages an active Quarto game session between two players.
 * Handles move validation, game state updates, and communication with clients.
 */
public class GameSession {

    /*@ private invariant player1 != null && player2 != null;
        private invariant game != null;
    @*/

    private final ClientHandler player1;
    private final ClientHandler player2;
    private final QuartoGame game;
    private /*@ spec_public @*/ boolean active;

    /**
     * Creates a new GameSession and starts the game.
     *
     * @param p1 the first player (ClientHandler).
     * @param p2 the second player (ClientHandler).
     */
    /*@ requires p1 != null && p2 != null;
        ensures this.player1 == p1;
        ensures this.player2 == p2;
        ensures this.active == true;
    @*/
    public GameSession(ClientHandler p1, ClientHandler p2) {
        this.player1 = p1;
        this.player2 = p2;
        this.game = new QuartoGame(new HumanPlayer(p1.getUsername()),
                new HumanPlayer(p2.getUsername()));
        this.active = true;

        startGame();
    }

    /**
     * Initializes the game by sending the NEWGAME packet to both players.
     */
    private void startGame() {
        String msg = Protocol.NEWGAME + Protocol.DELIMITER
                + player1.getUsername() + Protocol.DELIMITER
                + player2.getUsername();

        player1.sendMessage(msg);
        player2.sendMessage(msg);
        System.out.println("Game started: " + player1.getUsername() + " vs " + player2.getUsername());
    }

    /**
     * Handles a move request from a client.
     * Validates the move, updates the game state, and broadcasts the move or sends an error.
     *
     * @param sender the client sending the move.
     * @param packet the packet containing the move details.
     */
    /*@ requires sender != null && packet != null;
    @*/
    public synchronized void handleMove(ClientHandler sender, Packet packet) {
        if (!active) {
            return;
        }

        ClientHandler expectedPlayer = (game.getTurn() == game.players[0]) ? player1 : player2;

        if (sender != expectedPlayer) {
            sender.sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Not your turn");
            return;
        }

        try {
            if (packet.getArgCount() == 1) {
                if (game.getCurrentPiece() != null) {
                    sender.sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Invalid move format");
                    return;
                }

                int pieceId = Integer.parseInt(packet.getArg(0));

                if (pieceId >= 0 && pieceId <= 15) {
                    game.choosePiece(Piece.fromProtocolId(pieceId));
                    broadcastMove(packet);
                    if (!active) {
                        return;
                    }
                } else {
                    sender.sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Invalid piece ID");
                }

            } else if (packet.getArgCount() == 2) {
                int index = Integer.parseInt(packet.getArg(0));
                int nextPieceId = Integer.parseInt(packet.getArg(1));

                Piece pieceToPlace = game.getCurrentPiece();

                if (pieceToPlace == null) {
                    sender.sendMessage(Protocol.ERROR + Protocol.DELIMITER + "No piece to place. Choose a piece first.");
                    return;
                }

                QuartoMove move = new QuartoMove(pieceToPlace, index);

                if (!game.isValidMove(move)) {
                    sender.sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Illegal move (occupied)");
                    return;
                }

                game.doMove(move);
                broadcastMove(packet);

                if (!active) {
                    return;
                }

                // Game over: winner or draw. Check both isGameover() and board so we never miss a win.
                if (game.isGameover() || game.board.hasWinner() || game.board.isFull()) {
                    checkGameOver();
                    return;
                }

                if (!active) {
                    return;
                }

                if (nextPieceId >= 0 && nextPieceId <= 15) {
                    game.choosePiece(Piece.fromProtocolId(nextPieceId));
                }
                else if (nextPieceId == 16) {
                    ClientHandler winner = getOpponent(sender);
                    endGame("VICTORY", winner);
                }
                else if (nextPieceId == 17) {
                    // Last piece placed without claim (pieceId=17 means no pieces remain after this move)
                    // After doMove, if no pieces remain, the game should end (either victory or draw)
                    // Protocol says: "If M == 17, the player places the last piece without claiming Quarto.
                    // This is only allowed as the final move of the game, when no pieces remain."
                    if (game.getAvailablePieces().isEmpty()) {
                        // No pieces left - game should end (either victory or draw)
                        if (game.isGameover()) {
                            checkGameOver();
                        } else {
                            // Board is full but no winner - draw
                            endGame("DRAW", null);
                        }
                    } else {
                        // Pieces still remain - this is an error (17 is only allowed when no pieces remain)
                        sender.sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Invalid MOVE! Not a legal move.");
                    }
                }
                else {
                    sender.sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Invalid Piece ID");
                }

            } else {
                sender.sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Invalid arguments");
            }

        } catch (NumberFormatException e) {
            sender.sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Numbers required");
        } catch (Exception e) {
            sender.sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Error: " + e.getMessage());
        }
    }

    /**
     * Broadcasts the move packet to both players.
     *
     * @param packet the packet containing move arguments.
     */
    /*@ requires packet != null;
    @*/
    private void broadcastMove(Packet packet) {
        String msg = Protocol.MOVE;
        for (int i = 0; i < packet.getArgCount(); i++) {
            msg += Protocol.DELIMITER + packet.getArg(i);
        }
        player1.sendMessage(msg);
        player2.sendMessage(msg);
    }

    /**
     * Helper method to get the opponent of a given player.
     *
     * @param player the player whose opponent is needed.
     * @return the opponent ClientHandler.
     */
    /*@ requires player != null;
        ensures (player == player1 ==> \result == player2) && (player == player2 ==> \result == player1);
    @*/
    private ClientHandler getOpponent(ClientHandler player) {
        return (player == player1) ? player2 : player1;
    }


    /**
     * Gets the first player in the session.
     *
     * @return player1 ClientHandler.
     */
    /*@ pure @*/
    public ClientHandler getPlayer1() {
        return player1;
    }

    /**
     * Gets the second player in the session.
     *
     * @return player2 ClientHandler.
     */
    /*@ pure @*/
    public ClientHandler getPlayer2() {
        return player2;
    }

    /**
     * Checks if the game has ended and triggers the endgame sequence if so.
     */
    private void checkGameOver() {
        if (game.getWinner() != null) {
            Player winnerLogic = game.getWinner();
            ClientHandler winnerHandler = winnerLogic.getName().equals(player1.getUsername()) ? player1 : player2;
            endGame("VICTORY", winnerHandler);
        } else if (game.board.hasWinner()) {
            // Board has Quarto but getWinner() null (defensive) — winner is who just moved (getTurn())
            Player winnerLogic = game.getTurn();
            ClientHandler winnerHandler = winnerLogic.getName().equals(player1.getUsername()) ? player1 : player2;
            endGame("VICTORY", winnerHandler);
        } else if (game.board.isFull()) {
            endGame("DRAW", null);
        }
    }

    /**
     * Terminates the game session and notifies players of the result.
     *
     * @param reason the reason for game over (VICTORY, DRAW, DISCONNECT).
     * @param winner the winner of the game (can be null for DRAW).
     */
    /*@ requires reason != null;
        ensures active == false;
    @*/
    private void endGame(String reason, ClientHandler winner) {
        if (!active) return;
        active = false;

        StringBuilder msg = new StringBuilder(Protocol.GAMEOVER);
        msg.append(Protocol.DELIMITER).append(reason);
        if (winner != null) {
            msg.append(Protocol.DELIMITER).append(winner.getUsername());
        }

        String finalMsg = msg.toString();
        player1.sendMessage(finalMsg);
        player2.sendMessage(finalMsg);

        player1.getServer().onGameEnded(player1, player2);
    }

    /**
     * Handles player disconnection during an active game.
     * Declares the opponent as the winner.
     *
     * @param disconnectedClient the client who disconnected.
     */
    /*@ requires disconnectedClient != null;
    @*/
    public synchronized void playerDisconnected(ClientHandler disconnectedClient) {
        if (!active) {
            player1.getServer().onGameEnded(player1, player2);
            return;
        }
        ClientHandler winner = getOpponent(disconnectedClient);
        endGame("DISCONNECT", winner);
    }
}