package utwente.module2.quarto.networking;

/**
 * Defines the protocol constants used for network communication between the Quarto client and server.
 * Contains command strings and the delimiter used for message parsing.
 */
public class Protocol {
    /**
     * Handshake command sent by client/server to initiate connection.
     */
    public static final String HELLO = "HELLO";

    /**
     * Command sent by client to log in with a username.
     */
    public static final String LOGIN = "LOGIN";

    /**
     * Command sent by client to join a game lobby/queue.
     */
    public static final String QUEUE = "QUEUE";

    /**
     * Command representing a game move (placing a piece or selecting the next one).
     */
    public static final String MOVE = "MOVE";

    /**
     * Command sent when an error occurs or an invalid action is attempted.
     */
    public static final String ERROR = "ERROR";

    /**
     * Command sent by server to indicate a new game has started.
     */
    public static final String NEWGAME = "NEWGAME";

    /**
     * The character used to separate command arguments in a message.
     */
    public static final String DELIMITER = "~";

    /**
     * Command sent by client to request a list of connected players.
     */
    public static final String LIST = "LIST";

    /**
     * Command sent by server to indicate the game has ended.
     */
    public static final String GAMEOVER = "GAMEOVER";

    /**
     * Error response sent by server if the requested username is already taken.
     */
    public static final String ALREADYLOGGEDIN = "ALREADYLOGGEDIN";
}