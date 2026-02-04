package utwente.module2.quarto.networking;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;

/**
 * An abstract class representing a network connection.
 * Handles the low-level details of sending and receiving messages over a socket.
 */
public abstract class Connection {

    /*@ private invariant socket != null;
        private invariant in != null;
        private invariant out != null;
    @*/


    private final Socket socket;
    private final BufferedReader in;
    private final BufferedWriter out;
    private /*@ spec_public @*/ boolean started = false;

    /**
     * Creates a new Connection using an existing socket.
     *
     * @param socket the socket to wrap.
     * @throws IOException if input/output streams cannot be created.
     */
    /*@ requires socket != null;
        ensures this.socket == socket;
        ensures !started;
    @*/
    public Connection(Socket socket) throws IOException {
        this.socket = socket;
        this.in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
        this.out = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
    }

    /**
     * Creates a new Connection by connecting to a host and port.
     *
     * @param host the address to connect to.
     * @param port the port to connect to.
     * @throws IOException if the connection cannot be established.
     */
    /*@ requires host != null && port >= 0 && port <= 65535;
        ensures !started;
    @*/
    public Connection(InetAddress host, int port) throws IOException {
        this(new Socket(host, port));
    }

    /**
     * Starts the message receiving thread.
     * Can only be called once.
     *
     * @throws IllegalStateException if the connection has already been started.
     */
    /*@ requires !started;
        ensures started;
    @*/
    public void start() {
        if (started) {
            throw new IllegalStateException("Cannot start a Connection twice");
        }
        started = true;
        new Thread(this::receiveMessages).start();
    }

    /**
     * Internal loop that continuously reads messages from the socket.
     * Dispatches received messages to handleMessage().
     */
    private void receiveMessages() {
        handleStart();
        try {
            String inputLine;
            while ((inputLine = in.readLine()) != null) {
                handleMessage(inputLine);
            }
        } catch (IOException e) {
            // Connection interrupted or closed
        } finally {
            close();
            handleDisconnect();
        }
    }

    /**
     * Sends a message over the network.
     * Appends a newline and flushes the stream.
     *
     * @param message the message to send.
     * @return true if sent successfully, false otherwise.
     */
    /*@ requires message != null;
    @*/
    public boolean sendMessage(String message) {
        try {
            out.write(message);
            out.newLine();
            out.flush();
            return true;
        } catch (IOException e) {
            close();
            return false;
        }
    }

    /**
     * Closes the underlying socket and streams.
     */
    /*@ ensures socket.isClosed();
    @*/
    public void close() {
        try {
            socket.close();
        } catch (IOException ignored) {}
    }

    /**
     * Hook method called when the connection thread starts.
     * Can be overridden by subclasses.
     */
    protected void handleStart() {
        // Default implementation does nothing
    }

    /**
     * Returns the underlying socket of this connection.
     * @return the socket
     */
    /*@
        ensures \result != null;
        pure;
    @*/
    public java.net.Socket getSocket() {
        return socket;
    }

    /**
     * Abstract method to handle incoming messages.
     * Must be implemented by subclasses to define protocol logic.
     *
     * @param message the received message.
     */
    /*@ requires message != null;
    @*/
    protected abstract void handleMessage(String message);

    /**
     * Abstract method called when the connection is closed or lost.
     * Must be implemented by subclasses to handle cleanup.
     */
    protected abstract void handleDisconnect();
}