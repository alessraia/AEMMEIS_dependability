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

public class SedeDAOTest {

    @Test
    public void testDoRetrieveById_found() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeQuery()).thenReturn(rs);
        when(rs.next()).thenReturn(true);
        when(rs.getInt(1)).thenReturn(5);
        when(rs.getString(2)).thenReturn("Milano");
        when(rs.getString(3)).thenReturn("Via X");
        when(rs.getInt(4)).thenReturn(12);
        when(rs.getString(5)).thenReturn("20100");

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            SedeDAO spy = spy(new SedeDAO());
            doReturn(Collections.emptyList()).when(spy).getPresenza(5);

            Sede s = spy.doRetrieveById(5);

            assertNotNull(s);
            assertEquals(5, s.getIdSede());
            assertEquals("Milano", s.getCitta());
            assertEquals("Via X", s.getVia());
            assertEquals(12, s.getCivico());
            assertEquals("20100", s.getCap());
            assertEquals(0, s.getLibri().size());
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
        when(rs.getString(2)).thenReturn("C1", "C2");
        when(rs.getString(3)).thenReturn("V1", "V2");
        when(rs.getInt(4)).thenReturn(10, 20);
        when(rs.getString(5)).thenReturn("10000", "20000");

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            SedeDAO spy = spy(new SedeDAO());
            doReturn(Collections.emptyList()).when(spy).getPresenza(anyInt());

            List<Sede> list = spy.doRetrivedAll();

            assertNotNull(list);
            assertEquals(2, list.size());
            assertEquals(1, list.get(0).getIdSede());
            assertEquals(2, list.get(1).getIdSede());
        }
    }

    @Test
    public void testAddLibroSede_addsBookAndCallsLibroDAO() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(1);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            Sede sede = new Sede();
            sede.setIdSede(42);
            sede.setLibri(new ArrayList<>());

            Libro l = new Libro();
            l.setIsbn("ABCD");

            try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                    (mock, ctx) -> when(mock.doRetrieveById("ABCD")).thenReturn(l))) {

                SedeDAO dao = new SedeDAO();
                dao.addLibroSede(sede, "ABCD");

                verify(ps).setInt(1, 42);
                verify(ps).setString(2, "ABCD");
                verify(ps).executeUpdate();

                assertEquals(1, sede.getLibri().size());
                assertEquals("ABCD", sede.getLibri().get(0).getIsbn());
            }
        }
    }

}
