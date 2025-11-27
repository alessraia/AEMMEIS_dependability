package controller.utente;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import model.utenteService.Utente;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.List;

import static org.mockito.Mockito.*;
import static org.junit.jupiter.api.Assertions.*;

class RicercaServletTest {
    private RicercaServlet servletUnderTest;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private LibroDAO libroDAOMock;
    private Utente utenteMock;

    @BeforeEach
    void setUp() {
        servletUnderTest = new RicercaServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        libroDAOMock = mock(LibroDAO.class);
        utenteMock = mock(Utente.class);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(utenteMock);
        when(utenteMock.getTipo()).thenReturn("");

        servletUnderTest.setLibroDAO(libroDAOMock);
    }

    @Test
    void testDoGet_UserIsAdmin() throws ServletException, IOException {
        when(utenteMock.getTipo()).thenReturn("Gestore");
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp")).thenReturn(dispatcher);

        servletUnderTest.doGet(request, response);

        verify(request).getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp");
        verify(dispatcher).forward(request, response);
    }

    @Test
    void testDoGet_SearchWithResults_ForwardsAndSetsAttributes() throws ServletException, IOException {
        when(request.getParameter("q")).thenReturn("keyword");
        Libro l1 = mock(Libro.class);
        when(l1.getIsbn()).thenReturn("isbn1");
        when(l1.getTitolo()).thenReturn("titolo1");
        when(libroDAOMock.Search("keyword")).thenReturn(List.of(l1));

        RequestDispatcher dispatcher = mock(RequestDispatcher.class);
        when(request.getRequestDispatcher("/WEB-INF/results/ricerca.jsp")).thenReturn(dispatcher);

        servletUnderTest.doGet(request, response);

        verify(request).setAttribute(eq("results"), any());
        verify(request).setAttribute("q", "keyword");
        verify(request).getRequestDispatcher("/WEB-INF/results/ricerca.jsp");
        verify(dispatcher).forward(request, response);
    }

    @Test
    void testDoGet_EmptyQuery_ForwardsToIndex() throws ServletException, IOException {
        when(request.getParameter("q")).thenReturn("");
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);
        when(request.getRequestDispatcher("index.html")).thenReturn(dispatcher);

        servletUnderTest.doGet(request, response);

        verify(request).getRequestDispatcher("index.html");
        verify(dispatcher).forward(request, response);
    }

    /**
     * Test to kill mutation at line 30: negated conditional on getLibroDAO() != null
     * This test verifies the ternary operator by checking that when LibroDAO is set to null,
     * the getLibroDAO method returns null (testing the condition explicitly).
     */
    @Test
    void testGetLibroDAO_WhenSetToNull_ReturnsNull() {
        servletUnderTest.setLibroDAO(null);
        
        LibroDAO actualDAO = servletUnderTest.getLibroDAO();
        
        assertNull(actualDAO, "getLibroDAO should return null when explicitly set to null");
    }

    /**
     * Test to kill mutation at line 58: replaced return value with null for getLibroDAO
     * This test verifies that getLibroDAO correctly returns the injected LibroDAO instance.
     */
    @Test
    void testGetLibroDAO_ReturnsInjectedInstance() {
        LibroDAO expectedDAO = mock(LibroDAO.class);
        servletUnderTest.setLibroDAO(expectedDAO);

        LibroDAO actualDAO = servletUnderTest.getLibroDAO();

        assertNotNull(actualDAO, "getLibroDAO should not return null when a DAO is injected");
        assertSame(expectedDAO, actualDAO, "getLibroDAO should return the same instance that was injected");
    }

    /**
     * Test to kill mutation at line 30: negated conditional in the ternary operator
     * This test exercises the doGet method when getLibroDAO() != null condition is true,
     * ensuring the injected DAO is used instead of creating a new instance.
     */
    @Test
    void testDoGet_WithInjectedDAO_UsesInjectedInstance() throws ServletException, IOException {
        // Verify that when a DAO is injected, it's actually used
        LibroDAO injectedDAO = mock(LibroDAO.class);
        servletUnderTest.setLibroDAO(injectedDAO);
        
        when(request.getParameter("q")).thenReturn("testQuery");
        when(injectedDAO.Search("testQuery")).thenReturn(List.of());
        
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);
        when(request.getRequestDispatcher("/WEB-INF/results/ricerca.jsp")).thenReturn(dispatcher);

        servletUnderTest.doGet(request, response);

        // Verify the injected DAO's Search method was called (proving it was used)
        verify(injectedDAO).Search("testQuery");
        verify(dispatcher).forward(request, response);
    }
}
