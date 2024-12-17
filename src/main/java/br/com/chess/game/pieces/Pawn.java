package br.com.chess.game.pieces;

import br.com.chess.game.boardgame.Board;
import br.com.chess.game.boardgame.ChessPiece;
import br.com.chess.game.boardgame.Position;
import br.com.chess.game.chess.ChessMatch;
import br.com.chess.game.chess.utils.Color;

public class Pawn extends ChessPiece {

    private ChessMatch chessMatch; //@ in modelMatch;

    //@ public represents maxMove = 2;

    //@ public model ChessMatch modelMatch;
    //@ private represents modelMatch = this.chessMatch;

    /*@ public normal_behavior
     @     ensures modelMatch == chessMatch;
     @     ensures modelBoard == board;
     @     ensures modelColor == color;
     @ pure
     @*/
    public Pawn(Board board, Color color, ChessMatch chessMatch) {
        super(board, color);
        this.chessMatch = chessMatch;
    }

    @Override
    public boolean[][] possibleMoves() {
        boolean[][] mat = new boolean[getBoard().getRows()][getBoard().getColumns()];

        if (position == null || !getBoard().positionExists(position)) {
            return mat;
        }
      
        Position p = new Position(0, 0);

        // Define direções com base na cor da peça
        int direction = (getColor() == Color.WHITE) ? -1 : 1;
        int startRow = (getColor() == Color.WHITE) ? 6 : 1; // Linha inicial para o movimento duplo

        // Movimentos possíveis do peão
        int[][] directions = {
                {direction, 0},               // Movimento para frente
                {direction * 2, 0},           // Movimento duplo (apenas no primeiro movimento)
                {direction, -1},              // Captura à esquerda
                {direction, 1}                // Captura à direita
        };

        /*@ maintaining 0 <= i && i <= directions.length;
          @ maintaining mat.length == getBoard().getRows();
          @ maintaining mat[0].length == getBoard().getColumns();
          @ maintaining (\forall int x, y;
          @     0 <= x && x < mat.length && 0 <= y && y < mat[x].length;
          @     mat[x][y] ==> (
          @         getBoard().positionExistsBasic(x, y) &&
          @         (getBoard().pieces[x][y] == null ||
          @         (getBoard().pieces[x][y] instanceof ChessPiece &&
          @          getBoard().pieces[x][y].getColor() != this.getColor()))));
          @ decreases directions.length - i;
          @*/
        for (int i = 0; i < directions.length; i++) {
            int dx = directions[i][0];
            int dy = directions[i][1];

            p.setValues(position.getRow() + dx, position.getColumn() + dy);

            if (getBoard().positionExists(p)) {
                if (i == 0 && !getBoard().thereIsAPiece(p)) {
                    // Movimento simples para frente
                    mat[p.getRow()][p.getColumn()] = true;
                } else if (i == 1 && position.getRow() == startRow) {
                    // Movimento duplo
                    Position intermediate = new Position(position.getRow() + direction, position.getColumn());
                    if (!getBoard().thereIsAPiece(intermediate) && !getBoard().thereIsAPiece(p)) {
                        mat[p.getRow()][p.getColumn()] = true;
                    }
                } else if (i > 1 && isThereOpponentPiece(p)) {
                    // Captura à esquerda ou direita
                    mat[p.getRow()][p.getColumn()] = true;
                }
            }
        }

        // Movimentos especiais: en passant
        if ((getColor() == Color.WHITE && position.getRow() == 3) ||
                (getColor() == Color.BLACK && position.getRow() == 4)) {

            int[][] enPassantDirections = {
                    {0, -1}, // Esquerda
                    {0, 1}   // Direita
            };

            /*@ maintaining 0 <= j && j <= enPassantDirections.length;
              @ maintaining mat.length == getBoard().getRows();
              @ maintaining mat[0].length == getBoard().getColumns();
              @ decreases enPassantDirections.length - j;
              @*/
            for (int j = 0; j < enPassantDirections.length; j++) {
                int[] dir = enPassantDirections[j];
                p.setValues(position.getRow(), position.getColumn() + dir[1]);
                if (getBoard().positionExists(p) && isThereOpponentPiece(p)
                        && getBoard().piece(p) == chessMatch.getEnPassantVulnerable()) {

                    p.setValues(position.getRow() + direction, p.getColumn());
                    if(getBoard().positionExists(p)) {
                        mat[p.getRow()][p.getColumn()] = true;
                    }
                }
            }
        }
        return mat;
    }

    /*@ also
      @ public normal_behavior
      @     ensures \result.equals("P");
      @ pure
      @*/
    @Override
    public String getString(){
        return "P";
    }
}
