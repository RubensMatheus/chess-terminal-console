package br.com.chess.game.boardgame;

public abstract class Piece {

    protected /*@ nullable */ Position position; //@ in modelPosition;
    private Board board; //@ in modelBoard;

    //@ public model /*@ nullable */ Position modelPosition;
    //@ private represents modelPosition = this.position;

    //@ public model Board modelBoard;
    //@ private represents modelBoard = this.board;

    /*@ public normal_behavior
      @     ensures modelBoard == board;
      @     ensures modelPosition == null;
      @ pure
      @*/
    public Piece(Board board) {
        this.board = board;
        position = null;
    }

    /*@ public normal_behavior
      @     ensures \result == modelBoard;
      @ pure
      @*/
    public Board getBoard() {
        return board;
    }

    /*@ public normal_behavior
      @     ensures \result == modelPosition;
      @ pure
      @*/
    public /*@ nullable */ Position getPosition() {
        return position;
    }


    //@ assignable \nothing;
    public abstract boolean[][] possibleMoves();

    /*@ requires modelPosition != null;
      @ requires getBoard().positionExists(modelPosition);
      @ requires position.getRow() >= 0 && position.getRow() < modelBoard.getRows();
      @ requires position.getColumn() >= 0 && position.getColumn() < modelBoard.getColumns();
      @ assignable \nothing;
      @*/
    public boolean possibleMove(Position position) {
        return possibleMoves()[position.getRow()][position.getColumn()];
    }


    /*@ requires modelPosition != null;
      @ requires getBoard().positionExists(modelPosition);
      @ assignable \nothing;
      @*/
    public boolean isThereAnyPossibleMove() {
        boolean[][] mat = possibleMoves();
        for (boolean[] booleans : mat) {
            for (boolean aBoolean : booleans) {
                if (aBoolean) {
                    return true;
                }
            }
        }
        return false;
    }
}
