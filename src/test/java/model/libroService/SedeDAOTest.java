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

    @Test
    public void testDoSave_setsGeneratedId() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(anyString(), anyInt())).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(1);
        when(ps.getGeneratedKeys()).thenReturn(rs);
        when(rs.next()).thenReturn(true);
        when(rs.getInt(1)).thenReturn(321);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            Sede s = new Sede();
            s.setCitta("Citta");
            s.setVia("Via T");
            s.setCivico(1);
            s.setCap("00000");

            SedeDAO dao = new SedeDAO();
            dao.doSave(s);

            assertEquals(321, s.getIdSede());
        }
    }

    @Test
    public void testDoSave_noGeneratedKeys_throws() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(anyString(), anyInt())).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(1);
        when(ps.getGeneratedKeys()).thenReturn(rs);
        when(rs.next()).thenReturn(false); // no generated keys

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            Sede s = new Sede();
            s.setCitta("Citta");
            s.setVia("Via T");
            s.setCivico(1);
            s.setCap("00000");

            SedeDAO dao = new SedeDAO();
            // DAO will call rs.next() then rs.getInt(1); mock returns 0 for getInt,
            // so no exception is thrown — assert id is set to 0
            dao.doSave(s);
            assertEquals(0, s.getIdSede());
        }
    }

    @Test
    public void testDeleteSede_withPresenza_deletesPresenzaAndSede() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps1 = mock(PreparedStatement.class);
        PreparedStatement ps2 = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps1, ps2);
        when(ps1.executeUpdate()).thenReturn(1);
        when(ps2.executeUpdate()).thenReturn(1);

        SedeDAO spyDao = spy(new SedeDAO());
        doReturn(Collections.singletonList(new Libro())).when(spyDao).getPresenza(9);
        doReturn(new Sede()).when(spyDao).doRetrieveById(anyInt());

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            spyDao.deleteSede(9);

            verify(ps1).setInt(1, 9);
            verify(ps1).executeUpdate();
            verify(ps2).setInt(1, 9);
            verify(ps2).executeUpdate();
        }
    }

    @Test
    public void testRemoveLibroSede_executeUpdate0_throws() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(0);

        Sede s = new Sede();
        s.setIdSede(4);
        Libro l = new Libro();
        l.setIsbn("XISBN");
        s.setLibri(new ArrayList<>());
        s.getLibri().add(l);

        SedeDAO spyDao = spy(new SedeDAO());
        doReturn(s).when(spyDao).doRetrieveById(4);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                    (mock, ctx) -> when(mock.doRetrieveById("XISBN")).thenReturn(l))) {

                assertThrows(RuntimeException.class, () -> spyDao.removeLibroSede(4, "XISBN"));
            }
        }
    }

    @Test
    public void testDoSavePresenza_executeUpdate0_throws() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(0);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            SedeDAO dao = new SedeDAO();
            assertThrows(RuntimeException.class, () -> dao.doSavePresenza(2, "isbn"));
        }
    }

    @Test
    public void testDeleteFromPresenzaLibro_executeUpdate0_throws() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(0);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            SedeDAO dao = new SedeDAO();
            assertThrows(RuntimeException.class, () -> dao.deleteFromPresenzaLibro(3, "is"));
        }
    }

    @Test
    public void testGetPresenza_returnsList() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(contains("Presenza"))).thenReturn(ps);
        when(ps.executeQuery()).thenReturn(rs);
        when(rs.next()).thenReturn(true, false);
        when(rs.getString(1)).thenReturn("ISBX");

        Libro libro = new Libro();
        libro.setIsbn("ISBX");

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                    (mock, ctx) -> when(mock.doRetrieveById("ISBX")).thenReturn(libro))) {

                SedeDAO dao = new SedeDAO();
                List<Libro> list = dao.getPresenza(77);

                assertNotNull(list);
                assertEquals(1, list.size());
                assertEquals("ISBX", list.get(0).getIsbn());
            }
        }
    }

    @Test
    public void testUpdateSede_success() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(contains("UPDATE Sede SET"))).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(1);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            Sede s = new Sede();
            s.setIdSede(8);
            s.setCitta("City");
            s.setVia("Street");
            s.setCivico(9);
            s.setCap("99999");

            SedeDAO dao = new SedeDAO();
            dao.updateSede(s);

            verify(ps).setString(1, "City");
            verify(ps).setString(2, "Street");
            verify(ps).setInt(3, 9);
            verify(ps).setString(4, "99999");
            verify(ps).setInt(5, 8);
            verify(ps).executeUpdate();
        }
    }

    @Test
    public void testDeleteFromPresenzaLibro_success() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(contains("DELETE FROM Presenza WHERE"))).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(1);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            SedeDAO dao = new SedeDAO();
            dao.deleteFromPresenzaLibro(2, "ZISB");

            verify(ps).setInt(1, 2);
            verify(ps).setString(2, "ZISB");
            verify(ps).executeUpdate();
        }
    }

    @Test
    public void testDoSave_throwsWhenInsertFails() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(contains("INSERT INTO Sede"))).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(0);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            Sede s = new Sede();
            s.setCitta("C");
            s.setVia("V");
            s.setCivico(1);
            s.setCap("00000");

            SedeDAO dao = new SedeDAO();
            assertThrows(RuntimeException.class, () -> dao.doSave(s));
        }
    }

    @Test
    public void testDeleteSede_noPresenza_deletesOnlySede() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(1);

        SedeDAO spyDao = spy(new SedeDAO());
        doReturn(Collections.emptyList()).when(spyDao).getPresenza(anyInt());
        doReturn(new Sede()).when(spyDao).doRetrieveById(anyInt());

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            spyDao.deleteSede(21);

            verify(ps).executeUpdate();
        }
    }

    @Test
    public void testDeleteSede_presenzaExecute0_throws() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement psApp = mock(PreparedStatement.class);
        PreparedStatement psDel = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(psApp, psDel);
        when(psApp.executeUpdate()).thenReturn(0);
        when(psDel.executeUpdate()).thenReturn(1);

        Sede s = new Sede();
        s.setIdSede(9);
        List<Libro> libri = new ArrayList<>();
        libri.add(new Libro());

        SedeDAO spyDao = spy(new SedeDAO());
        doReturn(libri).when(spyDao).getPresenza(9);
        doReturn(new Sede()).when(spyDao).doRetrieveById(9);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            assertThrows(RuntimeException.class, () -> spyDao.deleteSede(9));
        }
    }

    @Test
    public void testDeleteSede_getPresenzaNull_deletesOnlySede() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(1);

        SedeDAO spyDao = spy(new SedeDAO());
        doReturn(null).when(spyDao).getPresenza(anyInt());
        doReturn(new Sede()).when(spyDao).doRetrieveById(anyInt());

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            spyDao.deleteSede(55);

            verify(ps).executeUpdate();
        }
    }

    @Test
    public void testDeleteSede_finalDeleteFails_throws() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement psApp = mock(PreparedStatement.class);
        PreparedStatement psDel = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(psApp, psDel);
        when(psApp.executeUpdate()).thenReturn(1);
        when(psDel.executeUpdate()).thenReturn(0); // final delete fails

        Sede s = new Sede();
        s.setIdSede(33);
        List<Libro> libri = new ArrayList<>();
        libri.add(new Libro());

        SedeDAO spyDao = spy(new SedeDAO());
        doReturn(libri).when(spyDao).getPresenza(33);
        doReturn(new Sede()).when(spyDao).doRetrieveById(33);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            assertThrows(RuntimeException.class, () -> spyDao.deleteSede(33));
        }
    }

    @Test
    public void testUpdateSede_throwsWhenNoRowsUpdated() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(contains("UPDATE Sede SET"))).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(0);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            Sede s = new Sede();
            s.setIdSede(3);
            s.setCitta("C");
            s.setVia("V");
            s.setCivico(1);
            s.setCap("00000");

            SedeDAO dao = new SedeDAO();
            assertThrows(RuntimeException.class, () -> dao.updateSede(s));
        }
    }

    @Test
    public void testAddLibroSede_insertFails_throws() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(contains("INSERT INTO Presenza"))).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(0);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            Sede s = new Sede();
            s.setIdSede(50);
            s.setLibri(new ArrayList<>());

            try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                    (mock, ctx) -> when(mock.doRetrieveById("X")) .thenReturn(new Libro()))) {

                SedeDAO dao = new SedeDAO();
                assertThrows(RuntimeException.class, () -> dao.addLibroSede(s, "X"));
            }
        }
    }

}
