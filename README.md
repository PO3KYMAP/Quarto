# 🎲 Quarto Game - Networked Java Project

A robust, multi-client implementation of the strategic board game **Quarto**. This project features a concurrent TCP
server, a responsive GUI (JavaFX), a lightweight TUI, and a smart AI opponent capable of playing autonomously.

---

## 🔥 Key Features

### 🖥️ Client-Server Architecture

- **Multi-threaded Server:** Handles multiple simultaneous game sessions via `ClientHandler` threads.
- **Matchmaking:** Single global queue; clients send `QUEUE` to join, again to leave. Two waiting clients start a game automatically.
- **Custom Protocol:** Text-based TCP protocol handling `LOGIN`, `QUEUE`, `MOVE`, `LIST`, and `HELLO` commands.
- **Robustness:** Handles client disconnects, invalid moves, and concurrency gracefully.

### 🤖 Advanced AI (Bot)

- **Smart Strategy:**
    - **Placement Phase:** Detects immediate winning moves (1-ply lookahead) to seize victory.
    - **Selection Phase:** Analyzes available pieces to avoid giving the opponent a winning piece ("Safe Piece"
      heuristic).
- **Naive Strategy:** Random moves for testing and easy difficulty.
- **Interactive Launcher:** CLI tool to spawn bots with custom name and strategy; bot joins the matchmaking queue.

### 🎮 User Interfaces

- **GUI (JavaFX):**
    - Visual representation of the board and pieces.
    - Join queue / Leave queue for matchmaking.
- **TUI (Console):**
    - Lightweight, text-based interface for terminal usage.
    - Full support for all game commands and visual board representation using ASCII/Unicode.

---

## 🚀 Getting Started

### Prerequisites

- **Java JDK 17** or higher (Java 21/25 recommended).
- **JavaFX SDK** (Required for GUI).
- **Maven** (Optional, for dependency management).

### 🛠️ Compiling

**Option 1: Using Maven**

```bash
mvn clean install

```

**Option 2: Manual Compilation**
Ensure all `.java` files in `src` are compiled and the JavaFX library path is correctly set.

---

## 🕹️ How to Run

### 1. Start the Server 🌐

The server must be running first to accept connections.

```bash
java utwente.module2.quarto.server.QuartoServer
# Follow the prompt to enter a port (e.g., 1337)

```

### 2. Run the GUI Client 🎨

To start the graphical interface for human players.
*Note: Replace `/path/to/javafx/lib` with your actual JavaFX SDK path.*

```bash
java --module-path /path/to/javafx/lib --add-modules javafx.controls,javafx.fxml utwente.module2.quarto.client.QuartoGUI

```

### 3. Run the AI Bot 🤖

To spawn a computer player. The launcher will ask for Port, Strategy (Smart/Naive), and Bot name. The bot joins the matchmaking queue.

```bash
java utwente.module2.quarto.ai.AIClient

```

### 4. Run the TUI (Optional) 💻

```bash
java utwente.module2.quarto.client.QuartoTUI

```

---

## 🧠 Project Structure

```text
src/utwente/module2/quarto
├── ai              # ComputerPlayer logic (Smart/Naive strategies, AIClient)
├── client          # Client applications (GUI, TUI, NetworkListener)
├── gamelogic       # Core game rules (Board, Piece, Validation, GameSession)
├── networking      # Shared network classes (Packet, Protocol, Connection)
└── server          # Server logic (QuartoServer, ClientHandler)

```

---

## 📡 Protocol Overview

The communication follows a strict text-based protocol (base specification):

| Command | Arguments       | Description                                         |
|---------|-----------------|-----------------------------------------------------|
| `HELLO` | `<client_type>` | Initial handshake to identify client type.          |
| `LOGIN` | `<username>`    | Registers the client with the server.               |
| `QUEUE` | —               | Joins the matchmaking queue; sending again leaves.  |
| `MOVE`  | `<idx> <id>`    | Places current piece at `idx` and picks piece `id`. |
| `LIST`  | —               | Requests a list of online players.                  |

---

## 👥 Authors

* **Module 2 Team** - *Bondan Sharloimov | Jesse van der Donk*
