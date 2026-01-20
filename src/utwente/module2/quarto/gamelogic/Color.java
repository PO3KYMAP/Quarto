package utwente.module2.quarto.gamelogic;

public enum Color {
    LIGHT,
    DARK;

    @Override
    public String toString() {
        return switch (this) {
            case LIGHT -> "Light";
            case DARK -> "DARK";
        };
    }
}
