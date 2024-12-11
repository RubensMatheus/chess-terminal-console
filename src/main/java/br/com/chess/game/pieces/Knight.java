package br.com.chess.game.pieces;


import br.com.chess.game.boardgame.Board;
import br.com.chess.game.boardgame.Piece;
import br.com.chess.game.boardgame.Position;
import br.com.chess.game.chess.ChessPiece;
import br.com.chess.game.chess.exceptions.ChessException;
import br.com.chess.game.chess.utils.Color;

public class Knight extends ChessPiece {

    //@ public represents maxMove = 2;

    public Knight(Board board, Color color) {
        super(board, color);
    }

    /*@ public normal_behavior
      @     ensures \result.equals("C");
      @ pure
      @*/
    public String getString(){
        return "C";
    }


    /*@ requires getBoard().positionExists(position);
      @ ensures \result == (getBoard().pieces[position.getRow()][position.getColumn()] == null ||
      @     (getBoard().pieces[position.getRow()][position.getColumn()] instanceof ChessPiece &&
      @     ((ChessPiece) getBoard().pieces[position.getRow()][position.getColumn()]).getColor() != this.getColor()));
      @ pure helper
      @*/
    private boolean canMove(Position position) {
        /*@ nullable */ Piece p = getBoard().piece(position);
        if (p == null) {
            return true;
        }
        if (!(p instanceof ChessPiece)) {
            return false;
        }
        ChessPiece piece = (ChessPiece) p;
        return piece.getColor() != getColor();
    }


    @Override
    public boolean[][] possibleMoves() {

        boolean[][] mat = new boolean[getBoard().getRows()][getBoard().getColumns()];
        Position p = new Position(0, 0);

        int[][] directions = {
                {-1, -2}, {-2, -1}, {-2, 1}, {-1, 2},
                {1, 2}, {2, 1}, {2, -1}, {1, -2}
        };

        /*@ maintaining 0 <= i && i <= directions.length;
          @ maintaining (\forall int k; 0 <= k && k < i;
          @    position.getRow() + directions[k][0] >= 0 &&
          @    position.getRow() + directions[k][0] < getBoard().getRows() &&
          @    position.getColumn() + directions[k][1] >= 0 &&
          @    position.getColumn() + directions[k][1] < getBoard().getColumns() ==>
          @      mat[position.getRow() + directions[k][0]][position.getColumn() + directions[k][1]] ==
          @        (getBoard().pieces[position.getRow() + directions[k][0]][position.getColumn() + directions[k][1]] == null ||
          @        (getBoard().pieces[position.getRow() + directions[k][0]][position.getColumn() + directions[k][1]] instanceof ChessPiece &&
          @        ((ChessPiece) getBoard().pieces[position.getRow() + directions[k][0]][position.getColumn() + directions[k][1]]).getColor() != this.getColor())));
          @ decreasing directions.length - i;
          @*/
        for (int i = 0; i < directions.length; i++) {
            int dx = directions[i][0];
            int dy = directions[i][1];

            p.setValues(position.getRow() + dx, position.getColumn() + dy);
            if (getBoard().positionExists(p)) {
                //@ assert getBoard().positionExists(p);
                mat[p.getRow()][p.getColumn()] = canMove(p);
            }
        }

        return mat;
    }


}

