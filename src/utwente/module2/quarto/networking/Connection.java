package utwente.module2.quarto.networking;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;


public abstract class Connection {
    private final Socket socket;
    private final BufferedReader in;
    private final BufferedWriter out;
    private boolean started = false;

    public Connection(Socket socket) throws IOException {
        this.socket = socket;
        this.in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
        this.out = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
    }

    public Connection(InetAddress host, int port) throws IOException {
        this(new Socket(host, port));
    }

    public void start() {
        if (started) {
            throw new IllegalStateException("Cannot start a Connection twice");
        }
        started = true;
        new Thread(this::receiveMessages).start();
    }

    private void receiveMessages() {
        handleStart();
        try {
            String inputLine;
            while ((inputLine = in.readLine()) != null) {
                handleMessage(inputLine);
            }
        } catch (IOException e) {
        } finally {
            close();
            handleDisconnect();
        }
    }

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

    public void close() {
        try {
            socket.close();
        } catch (IOException ignored) {}
    }

    protected void handleStart() {
    }

    protected abstract void handleMessage(String message);

    protected abstract void handleDisconnect();
}