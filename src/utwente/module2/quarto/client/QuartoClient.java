package utwente.module2.quarto.client;

import utwente.module2.quarto.networking.Connection;
import utwente.module2.quarto.networking.Packet;
import utwente.module2.quarto.networking.Protocol;

import java.io.IOException;
import java.net.InetAddress;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;

/**
 * The client-side connection handler for the Quarto game.
 * Manages the protocol state (handshake, login) and dispatches received events to listeners.
 */
public class QuartoClient extends Connection {

    /*@ private invariant listeners != null;
    @*/

    private final List<NetworkListener> listeners = new ArrayList<>();
    private /*@ spec_public @*/ String myName;
    private /*@ spec_public @*/ boolean handshakeSent = false;

    /**
     * Creates a new QuartoClient and connects to the specified host and port.
     *
     * @param host     the server address.
     * @param port     the server port.
     * @param listener the initial listener for network events.
     * @throws IOException if the connection cannot be established.
     */
    /*@ requires host != null && port >= 0 && listener != null;
        ensures listeners.contains(listener);
    @*/
    public QuartoClient(InetAddress host, int port, NetworkListener listener) throws IOException {
        super(host, port);
        addListener(listener);
    }

    /**
     * Constructor for testing purposes or pre-connected sockets.
     * @param socket the socket to use.
     * @param listener the listener to add.
     * @throws IOException if streams cannot be created.
     */
    public QuartoClient(Socket socket, NetworkListener listener) throws IOException {
        super(socket);
        addListener(listener);
    }

    public void addListener(NetworkListener listener) {
        listeners.add(listener);
    }

    /**
     * Gets the username of this client.
     *
     * @return the username, or null if not logged in.
     */
    /*@ pure @*/
    public String getMyName() {
        return myName;
    }

    /**
     * Sends a login request to the server.
     * Automatically handles the HELLO handshake if it hasn't been sent yet.
     *
     * @param username the username to log in with.
     */
    /*@ requires username != null;
        ensures handshakeSent == true;
        ensures myName == username;
    @*/
    public void login(String username) {
        this.myName = username;
        if (!handshakeSent) {
            sendMessage(Protocol.HELLO + Protocol.DELIMITER + "JavaClient");
            handshakeSent = true;
        }
        sendMessage(Protocol.LOGIN + Protocol.DELIMITER + username);
    }

    /**
     * Sends a request to join or leave the matchmaking queue.
     * Sending QUEUE again removes the client from the queue. No reply is sent by the server.
     */
    public void queue() {
        sendMessage(Protocol.QUEUE);
    }

    /**
     * Joins the matchmaking queue. Equivalent to {@link #queue()} for the base protocol.
     *
     * @param lobbyName ignored in base protocol (single global queue).
     */
    public void joinLobby(String lobbyName) {
        queue();
    }

    /**
     * Requests the list of connected players from the server.
     */
    public void requestList() {
        sendMessage(Protocol.LIST);
    }

    /**
     * Sends a move to the server.
     *
     * @param index   the board index to place a piece (-1 if only selecting).
     * @param pieceId the ID of the piece to place (or select).
     */
    /*@ requires index >= -1 && index < 16;
        requires pieceId >= 0 && pieceId <= 16;
    @*/
    public void sendMove(int index, int pieceId) {
        if (index == -1) {
            sendMessage(Protocol.MOVE + Protocol.DELIMITER + pieceId);
        } else {
            sendMessage(Protocol.MOVE + Protocol.DELIMITER + index + Protocol.DELIMITER + pieceId);
        }
    }

    /**
     * Sends a queue request. Equivalent to {@link #queue()} for the base protocol.
     *
     * @param lobby ignored in base protocol.
     */
    public void sendQueue(String lobby) {
        queue();
    }

    /**
     * Processes incoming messages from the server and notifies listeners.
     *
     * @param message the raw protocol message.
     */
    /*@ requires message != null;
    @*/
    @Override
    protected void handleMessage(String message) {
        Packet packet = new Packet(message);
        String cmd = packet.getCommand();

        switch (cmd) {
            case Protocol.HELLO:
                for (NetworkListener l : listeners) l.onConnected();
                break;

            case Protocol.LOGIN:
                System.out.println("✅ Logged in successfully as " + myName);
                for (NetworkListener l : listeners) l.onLoginSuccess();
                break;

            case Protocol.ALREADYLOGGEDIN:
                this.myName = null;
                for (NetworkListener l : listeners) l.onError("Username already taken! Login again");
                break;

            case Protocol.NEWGAME:
                if (packet.getArgCount() >= 2) {
                    String p1 = packet.getArg(0);
                    String p2 = packet.getArg(1);

                    boolean amIStarting = p1.equals(myName);
                    String opponent = amIStarting ? p2 : p1;

                    for (NetworkListener l : listeners) {
                        l.onGameStarted(opponent, amIStarting);
                    }
                }
                break;

            case Protocol.MOVE:
                handleMoveCommand(packet);
                break;

            case Protocol.GAMEOVER:
                String reason = packet.getArg(0);
                String winner = (packet.getArgCount() > 1) ? packet.getArg(1) : "No one";
                System.out.println("[CLIENT] Received GAMEOVER: " + reason + ", Winner: " + winner);
                for (NetworkListener l : listeners) l.onGameOver(reason, winner);
                break;

            case Protocol.LIST:
                int splitIndex = message.indexOf(Protocol.DELIMITER);
                String info = (splitIndex != -1) ? message.substring(splitIndex + 1) : "";
                for (NetworkListener l : listeners) l.onListReceived(info);
                break;

            case Protocol.ERROR:
                String errorMsg = (packet.getArgCount() > 0) ? packet.getArg(0) : "Unknown Error";
                for (NetworkListener l : listeners) l.onError("Server Error: " + errorMsg);
                break;
        }
    }

    /**
     * Helper method to parse MOVE commands.
     *
     * @param packet the move packet.
     */
    private void handleMoveCommand(Packet packet) {
        int index = -1;
        int pieceId;

        try {
            if (packet.getArgCount() == 1) {
                pieceId = Integer.parseInt(packet.getArg(0));
            } else {
                index = Integer.parseInt(packet.getArg(0));
                pieceId = Integer.parseInt(packet.getArg(1));
            }

            for (NetworkListener l : listeners) l.onMoveReceived(index, pieceId);

        } catch (NumberFormatException ignored) {
            // Ignore invalid move formats
        }
    }

    /**
     * Notifies listeners when the connection is lost.
     */
    @Override
    protected void handleDisconnect() {
        for (NetworkListener l : listeners) l.onError("Connection lost!");
    }

    /**
     * Starts the connection and adds a shutdown hook to ensure clean disconnection.
     */
    @Override
    public void start() {
        Runtime.getRuntime().addShutdownHook(new Thread(() -> {
            try {
                System.out.println("[CLIENT] Force closing connection...");
                close();
            } catch (Exception ignored) {}
        }));
        super.start();
    }

    @Override
    protected void handleStart() {
        // No specific action needed on start
    }
}