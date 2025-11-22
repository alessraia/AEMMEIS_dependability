package model.libroService;

import model.ConPool;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;
import org.mockito.MockedStatic;
import org.mockito.Mockito;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

public class RepartoDAOTest {

    @Test
    public void testDoRetrieveById_found() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeQuery()).thenReturn(rs);
        when(rs.next()).thenReturn(true);
        when(rs.getInt(1)).thenReturn(7);
        when(rs.getString(2)).thenReturn("NomeR");
        when(rs.getString(3)).thenReturn("Desc");
        when(rs.getString(4)).thenReturn("img.png");

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            RepartoDAO spy = spy(new RepartoDAO());
            doReturn(Collections.emptyList()).when(spy).getAppartenenza(7);

            Reparto r = spy.doRetrieveById(7);

            assertNotNull(r);
            assertEquals(7, r.getIdReparto());
            assertEquals("NomeR", r.getNome());
            assertEquals("Desc", r.getDescrizione());
            assertEquals(0, r.getLibri().size());
        }
    }

    @Test
    public void testDoRetrivedAll_returnsList() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeQuery()).thenReturn(rs);
        when(rs.next()).thenReturn(true, true, false);
        when(rs.getInt(1)).thenReturn(1, 2);
        when(rs.getString(2)).thenReturn("R1", "R2");
        when(rs.getString(3)).thenReturn("D1", "D2");
        when(rs.getString(4)).thenReturn("i1.png", "i2.png");

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            RepartoDAO spy = spy(new RepartoDAO());
            doReturn(Collections.emptyList()).when(spy).getAppartenenza(anyInt());

            List<Reparto> list = spy.doRetrivedAll();

            assertNotNull(list);
            assertEquals(2, list.size());
            assertEquals(1, list.get(0).getIdReparto());
            assertEquals(2, list.get(1).getIdReparto());
        }
    }

    @Test
    public void testAggiungiLibroReparto_addsBookAndCallsLibroDAO() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(1);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            Reparto reparto = new Reparto();
            reparto.setIdReparto(10);
            reparto.setLibri(new ArrayList<>());

            Libro l = new Libro();
            l.setIsbn("ISBNX");

            try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                    (mock, ctx) -> when(mock.doRetrieveById("ISBNX")).thenReturn(l))) {

                RepartoDAO dao = new RepartoDAO();
                dao.aggiungiLibroReparto(reparto, "ISBNX");

                verify(ps).setInt(1, 10);
                verify(ps).setString(2, "ISBNX");
                verify(ps).executeUpdate();

                // LibroDAO.doRetrieveById should have been called and libro added to reparto
                assertEquals(1, reparto.getLibri().size());
                assertEquals("ISBNX", reparto.getLibri().get(0).getIsbn());
            }
        }
    }

}
