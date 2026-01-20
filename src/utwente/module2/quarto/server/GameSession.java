package utwente.module2.quarto.server;

import utwente.module2.quarto.gamelogic.*;
import utwente.module2.quarto.networking.Packet;
import utwente.module2.quarto.networking.Protocol;
import utwente.module2.quarto.gamelogic.player.*;

/**
 * GameSession manages a single Quarto match between two players.
 */
public class GameSession {

    private final ClientHandler player1;
    private final ClientHandler player2;
    private final QuartoGame game;
    private final String lobbyName;
    private boolean active;

    public GameSession(ClientHandler p1, ClientHandler p2, String lobbyName) {
        this.player1 = p1;
        this.player2 = p2;
        this.lobbyName = lobbyName;
        this.game = new QuartoGame(new HumanPlayer(p1.getUsername()),
                new HumanPlayer(p2.getUsername()));
        this.active = true;

        startGame();
    }

    private void startGame() {
        String msg = Protocol.NEWGAME + Protocol.DELIMITER
                + player1.getUsername() + Protocol.DELIMITER
                + player2.getUsername();

        player1.sendMessage(msg);
        player2.sendMessage(msg);

        System.out.println("Game started: " + player1.getUsername() + " vs " + player2.getUsername());
    }

    public synchronized void handleMove(ClientHandler sender, Packet packet) {
        if (!active) return;

        ClientHandler expectedPlayer = (game.getTurn() == game.players[0]) ? player1 : player2;

        if (sender != expectedPlayer) {
            sender.sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Not your turn");
            return;
        }

        try {
            if (packet.getArgCount() == 1) {

                if (game.getCurrentPiece() != null) {
                    sender.sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Invalid move format (index missing)");
                    return;
                }

                int pieceId = Integer.parseInt(packet.getArg(0));
                Piece chosenPiece = Piece.fromProtocolId(pieceId);

                game.choosePiece(chosenPiece);

                broadcastMove(packet);

            }
            else if (packet.getArgCount() == 2) {
                int index = Integer.parseInt(packet.getArg(0));
                int nextPieceId = Integer.parseInt(packet.getArg(1));

                Piece pieceToPlace = game.getCurrentPiece();

                QuartoMove move = new QuartoMove(pieceToPlace, index);

                if (game.isValidMove(move)) {
                    game.doMove(move);

                    if (game.isGameover()) {
                        broadcastMove(packet);
                        checkGameOver();
                        return;
                    }

                    Piece nextPiece = Piece.fromProtocolId(nextPieceId);

                    try {
                        game.choosePiece(nextPiece);
                        broadcastMove(packet);
                    } catch (Exception e) {
                        sender.sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Invalid piece choice: " + e.getMessage());
                    }

                } else {
                    sender.sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Illegal move (cell occupied)");
                }
            } else {
                sender.sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Invalid arguments count");
            }

        } catch (NumberFormatException e) {
            sender.sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Numbers required");
        } catch (IllegalArgumentException e) {
            sender.sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Invalid piece ID or Index");
        } catch (IllegalStateException e) {
            sender.sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Game logic error: " + e.getMessage());
        }
    }

    private void broadcastMove(Packet packet) {
        String msg = Protocol.MOVE;
        for (int i = 0; i < packet.getArgCount(); i++) {
            msg += Protocol.DELIMITER + packet.getArg(i);
        }
        player1.sendMessage(msg);
        player2.sendMessage(msg);
    }

    private void checkGameOver() {
        if (game.getWinner() != null) {

            Player winnerLogic = game.getWinner();

            ClientHandler winner = winnerLogic.getName().equals(player1.getUsername()) ? player1 : player2;

            endGame("VICTORY", winner);

        }
        else if (game.board.isFull()) {
            endGame("DRAW", null);
        }
    }

    private void endGame(String reason, ClientHandler winner) {
        active = false;
        StringBuilder msg = new StringBuilder(Protocol.GAMEOVER);
        msg.append(Protocol.DELIMITER).append(reason);
        if (winner != null) {
            msg.append(Protocol.DELIMITER).append(winner.getUsername());
        }
        player1.sendMessage(msg.toString());
        player2.sendMessage(msg.toString());
        player1.getServer().onGameEnded(lobbyName, player1, player2);
    }

    public synchronized void playerDisconnected(ClientHandler disconnectedClient) {
        if (!active) return;
        active = false;
        ClientHandler winner = (disconnectedClient == player1) ? player2 : player1;
        String msg = Protocol.GAMEOVER + Protocol.DELIMITER + "DISCONNECT" + Protocol.DELIMITER + winner.getUsername();
        winner.sendMessage(msg);
        winner.getServer().onGameEnded(lobbyName, player1, player2);
    }
}