package utwente.module2.quarto.server;

import utwente.module2.quarto.networking.Connection;
import utwente.module2.quarto.networking.Packet;
import utwente.module2.quarto.networking.Protocol;

import java.io.IOException;
import java.net.Socket;

/**
 * Handles the communication with a single client.
 * This class processes incoming messages and manages the client's state.
 */
public class ClientHandler extends Connection {

    /*@ private invariant server != null; @*/

    private final QuartoServer server;
    private /*@ spec_public @*/ String username;
    private /*@ spec_public @*/ boolean helloExchanged = false;

    /**
     * Creates a new ClientHandler for a specific socket connection.
     *
     * @param socket the socket for this connection.
     * @param server reference to the main server instance.
     * @throws IOException if an I/O error occurs during initialization.
     */
    /*@ requires socket != null && server != null;
        ensures this.server == server;
        ensures this.helloExchanged == false;
        ensures this.username == null;
    @*/
    public ClientHandler(Socket socket, QuartoServer server) throws IOException {
        super(socket);
        this.server = server;
    }

    /**
     * Callback method called when the connection starts.
     */
    @Override
    protected void handleStart() {
        System.out.println("Connection started.");
    }

    /**
     * Processes a received message from the client.
     * Parses the message into a packet and delegates to the appropriate handler.
     *
     * @param message the raw string message received from the client.
     */
    /*@ requires message != null;
    @*/
    @Override
    protected void handleMessage(String message) {
        Packet packet = new Packet(message);
        String command = packet.getCommand();

        switch (command) {
            case Protocol.HELLO -> handleHello(packet);
            case Protocol.LOGIN -> handleLogin(packet);
            case Protocol.QUEUE -> handleQueue(packet);
            case Protocol.LIST -> handleList();
            case Protocol.MOVE -> handleMove(packet);
            case Protocol.ERROR -> {
                // Client reported an error, logic handled by logging
            }
            default -> sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Unknown command");
        }
    }

    /**
     * Handles the HELLO handshake command.
     *
     * @param packet the packet containing the command.
     */
    /*@ requires packet != null;
        ensures helloExchanged == true || \old(helloExchanged) == true;
    @*/
    private void handleHello(Packet packet) {
        if (helloExchanged) {
            sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Handshake already done");
            return;
        }
        sendMessage(Protocol.HELLO + Protocol.DELIMITER + "QuartoServer");
        helloExchanged = true;
    }

    /**
     * Handles the LOGIN command.
     * Validates handshake status and username availability.
     *
     * @param packet the packet containing the requested username.
     */
    /*@ requires packet != null;
        ensures \old(username) == null && server.isUsernameTaken(packet.getArg(0)) == false ==> username != null;
    @*/
    private void handleLogin(Packet packet) {
        if (!helloExchanged) {
            sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Handshake missing");
            return;
        }

        if (packet.getArgCount() < 1) {
            sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Missing username");
            return;
        }

        if (this.username != null) {
            sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Already logged in");
            return;
        }

        String requestedName = packet.getArg(0);

        if (server.isUsernameTaken(requestedName)) {
            sendMessage(Protocol.ALREADYLOGGEDIN);
        } else {
            this.username = requestedName;
            server.addClient(this);
            sendMessage(Protocol.LOGIN);
        }
    }

    /**
     * Handles the QUEUE command to join or leave the matchmaking queue.
     * Sending QUEUE again removes the client from the queue. No reply is sent.
     *
     * @param packet the packet (arguments ignored in base protocol).
     */
    /*@ requires packet != null;
    @*/
    private void handleQueue(Packet packet) {
        if (username == null) {
            sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Not logged in");
            return;
        }
        server.handleQueueCommand(this);
    }

    /**
     * Handles the LIST command to request the list of connected players.
     */
    private void handleList() {
        if (username == null) {
            sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Not logged in");
            return;
        }

        String listString = server.getPlayerListString();
        sendMessage(Protocol.LIST + Protocol.DELIMITER + listString);
    }
    /**
     * Gets the main server instance associated with this handler.
     *
     * @return the QuartoServer reference.
     */
    /*@ pure @*/
    public QuartoServer getServer() {
        return server;
    }

    /**
     * Handles the MOVE command to perform a game move.
     *
     * @param packet the packet containing move details.
     */
    /*@ requires packet != null;
    @*/
    private void handleMove(Packet packet) {
        if (username == null) {
            sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Not logged in");
            return;
        }

        server.handleMove(this, packet);
    }

    /**
     * Callback method called when the client disconnects.
     * Removes the client from the server logic.
     */
    @Override
    protected void handleDisconnect() {
        System.out.println("Client disconnected: " + (username != null ? username : "Unknown"));
        server.removeClient(this);
    }

    /**
     * Gets the username of the connected client.
     *
     * @return the username, or null if not yet logged in.
     */
    /*@ pure @*/
    public String getUsername() {
        return username;
    }
}