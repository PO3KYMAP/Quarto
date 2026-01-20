package utwente.module2.quarto.client;

public interface NetworkListener {
    /** Connected to server and handshake complete. */
    void onConnected();

    /** Received a list of players/lobbies from server. */
    void onListReceived(String listInfo);

    /** Game started against an opponent. */
    void onGameStarted(String opponentName);

    /** * Opponent made a move.
     * @param index Board index where piece was placed (or -1 if first move).
     * @param pieceId The ID of the piece chosen for the next turn.
     */
    void onMoveReceived(int index, int pieceId);

    /** Game ended. */
    void onGameOver(String reason, String winner);

    /** Received an error message. */
    void onError(String error);
}
