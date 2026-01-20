package utwente.module2.quarto.gamelogic;

import java.util.ArrayList;
import java.util.List;
import utwente.module2.quarto.gamelogic.player.Player;

public class QuartoGame implements Game {
    public final Board board;
    public final Player[] players;
    private int currentPlayer;
    private Piece currentPiece; // != null -> place_piece phase,
                                // == null -> choose_piece phase
    private final List<Piece> availablePieces;
    private Player winner;
    private boolean gameOver;

    public QuartoGame(Player p1, Player p2) {
        this.board = new Board();
        this.players = new Player[]{p1, p2};
        this.currentPlayer = 0;
        this.currentPiece = null; // first player chooses a piece
        this.gameOver = false;

        this.availablePieces = new ArrayList<>();

        for (Piece piece : Piece.values()) {
            availablePieces.add(piece);
        }
    }

    public QuartoGame(QuartoGame currentGame) {
        this.board = currentGame.board.deepCopy();
        this.players = currentGame.players;
        this.currentPlayer = currentGame.currentPlayer;
        this.currentPiece = currentGame.currentPiece;
        this.gameOver = currentGame.gameOver;
        this.availablePieces = currentGame.availablePieces;
    }


    @Override
    public boolean isGameover() {
        return gameOver;
    }

    @Override
    public Player getTurn() {
        return players[currentPlayer];
    }

    @Override
    public Player getWinner() {
        return winner;
    }

    public Piece getCurrentPiece() {
        return currentPiece;
    }

    public List<Piece> getAvailablePieces() {
        return new ArrayList<>(availablePieces);
    }

    @Override
    public List<? extends Move> getValidMoves() {
        List<QuartoMove> moves = new ArrayList<>();
        if (gameOver || currentPiece == null) {
            return moves;
        }

        for (int i = 0; i < Board.DIM * Board.DIM; i++) {
            if (board.isEmptyField(i)) {
                moves.add(new QuartoMove(currentPiece, i));
            }
        }
        return moves;
    }

    @Override
    public boolean isValidMove(Move move) {
        if (!(move instanceof QuartoMove quartoMove)) {
            return false;
        }

        if (gameOver || currentPiece == null) {
            return false;
        }

        return quartoMove.getPiece() == currentPiece
                && board.isEmptyField(quartoMove.getIndex());
    }

    @Override
    public void doMove(Move move) {
        QuartoMove quartoMove = (QuartoMove) move;

        board.setField(quartoMove.getIndex(), quartoMove.getPiece());
        availablePieces.remove(quartoMove.getPiece());

        if (board.hasWinner()) {
            winner = getTurn();
            gameOver = true;
            return;
        }

        if (board.isFull()) {
            gameOver = true;
            return;
        }

        // next player must choose a piece
        currentPiece = null;
    }

    public void choosePiece(Piece piece) {
        if (gameOver) {
            throw new IllegalStateException("Game is over");
        }

        if (currentPiece != null) {
            throw new IllegalStateException("Piece already chosen");
        }

        if (piece == null) {
            throw new IllegalArgumentException("Piece cannot be null");
        }

        currentPiece = piece;

        // choosing a piece ends the players turn
        currentPlayer = 1 - currentPlayer;
    }
}
