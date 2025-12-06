package controller.admin.gestisciReparti;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletConfig;
import jakarta.servlet.ServletContext;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.Reparto;
import model.libroService.RepartoDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.mockito.Mockito.*;

/**
 * Test class for InsertLibroRepartoServlet
 * Tests the functionality of inserting books into a department (Reparto)
 */
class InsertLibroRepartoServletTest {

    private InsertLibroRepartoServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RepartoDAO repartoDAO;

    @BeforeEach
    void setUp() throws Exception {
        servlet = new InsertLibroRepartoServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        repartoDAO = mock(RepartoDAO.class);
        
        // Initialize servlet with ServletConfig
        ServletConfig servletConfig = mock(ServletConfig.class);
        ServletContext servletContext = mock(ServletContext.class);
        when(servletConfig.getServletContext()).thenReturn(servletContext);
        servlet.init(servletConfig);
    }

    /**
     * Test successful insertion of a single book into reparto
     * Expected: aggiungiLibroReparto called once, redirect to gestisci-reparti
     */
    @Test
    void testDoGet_SingleBookInsertion() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("1");
        when(request.getParameterValues("isbn")).thenReturn(new String[]{"123-456-789"});

        Reparto reparto = new Reparto();
        reparto.setIdReparto(1);
        reparto.setNome("Narrativa");

        when(repartoDAO.doRetrieveById(1)).thenReturn(reparto);
        doNothing().when(repartoDAO).aggiungiLibroReparto(any(Reparto.class), anyString());

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        verify(repartoDAO, times(1)).doRetrieveById(1);
        verify(repartoDAO, times(1)).aggiungiLibroReparto(reparto, "123-456-789");
        verify(response).sendRedirect("gestisci-reparti");
    }

    /**
     * Test insertion of multiple books into reparto
     * Expected: aggiungiLibroReparto called for each book
     */
    @Test
    void testDoGet_MultipleBookInsertion() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("2");
        when(request.getParameterValues("isbn")).thenReturn(new String[]{
            "111-111-111",
            "222-222-222",
            "333-333-333"
        });

        Reparto reparto = new Reparto();
        reparto.setIdReparto(2);
        reparto.setNome("Saggistica");

        when(repartoDAO.doRetrieveById(2)).thenReturn(reparto);
        doNothing().when(repartoDAO).aggiungiLibroReparto(any(Reparto.class), anyString());

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        verify(repartoDAO, times(3)).doRetrieveById(2);
        verify(repartoDAO).aggiungiLibroReparto(reparto, "111-111-111");
        verify(repartoDAO).aggiungiLibroReparto(reparto, "222-222-222");
        verify(repartoDAO).aggiungiLibroReparto(reparto, "333-333-333");
        verify(response).sendRedirect("gestisci-reparti");
    }

    /**
     * Test when no books are selected (isbn parameter is null)
     * Expected: no database operations, redirect to gestisci-reparti
     */
    @Test
    void testDoGet_NoBookSelected() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("3");
        when(request.getParameterValues("isbn")).thenReturn(null);

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        verify(repartoDAO, never()).doRetrieveById(anyInt());
        verify(repartoDAO, never()).aggiungiLibroReparto(any(Reparto.class), anyString());
        verify(response).sendRedirect("gestisci-reparti");
    }

    /**
     * Test when isbn array is empty (not null, but zero length)
     * Expected: no database operations, redirect to gestisci-reparti
     */
    @Test
    void testDoGet_EmptyBookArray() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("4");
        when(request.getParameterValues("isbn")).thenReturn(new String[]{});

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        verify(repartoDAO, never()).doRetrieveById(anyInt());
        verify(repartoDAO, never()).aggiungiLibroReparto(any(Reparto.class), anyString());
        verify(response).sendRedirect("gestisci-reparti");
    }

    /**
     * Test when idReparto parameter is null
     * Expected: NumberFormatException
     */
    @Test
    void testDoGet_IdRepartoNull() throws Exception {
        when(request.getParameter("idReparto")).thenReturn(null);
        when(request.getParameterValues("isbn")).thenReturn(new String[]{"123-456"});
        RequestDispatcher errorDispatcher = mock(RequestDispatcher.class);
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/ErroreReparto.jsp")).thenReturn(errorDispatcher);

        servlet.setRepartoDAO(repartoDAO);
        servlet.doGet(request, response);

        verify(repartoDAO, never()).aggiungiLibroReparto(any(Reparto.class), anyString());
        verify(errorDispatcher).forward(request, response);
    }

    /**
     * Test when idReparto is not a valid number
     * Expected: NumberFormatException
     */
    @Test
    void testDoGet_IdRepartoInvalid() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("invalid");
        when(request.getParameterValues("isbn")).thenReturn(new String[]{"123-456"});
        RequestDispatcher errorDispatcher = mock(RequestDispatcher.class);
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/ErroreReparto.jsp")).thenReturn(errorDispatcher);

        servlet.setRepartoDAO(repartoDAO);
        servlet.doGet(request, response);

        verify(repartoDAO, never()).aggiungiLibroReparto(any(Reparto.class), anyString());
        verify(errorDispatcher).forward(request, response);
    }

    /**
     * Test with negative idReparto
     * Expected: processes the request (validation should be done elsewhere)
     */
    @Test
    void testDoGet_NegativeIdReparto() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("-1");
        when(request.getParameterValues("isbn")).thenReturn(new String[]{"ISBN-123"});

        Reparto reparto = new Reparto();
        reparto.setIdReparto(-1);

        when(repartoDAO.doRetrieveById(-1)).thenReturn(reparto);
        doNothing().when(repartoDAO).aggiungiLibroReparto(any(Reparto.class), anyString());

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        verify(repartoDAO).doRetrieveById(-1);
        verify(repartoDAO).aggiungiLibroReparto(reparto, "ISBN-123");
        verify(response).sendRedirect("gestisci-reparti");
    }

    /**
     * Test with zero as idReparto
     * Expected: processes the request
     */
    @Test
    void testDoGet_ZeroIdReparto() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("0");
        when(request.getParameterValues("isbn")).thenReturn(new String[]{"ISBN-000"});

        Reparto reparto = new Reparto();
        reparto.setIdReparto(0);

        when(repartoDAO.doRetrieveById(0)).thenReturn(reparto);
        doNothing().when(repartoDAO).aggiungiLibroReparto(any(Reparto.class), anyString());

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        verify(repartoDAO).doRetrieveById(0);
        verify(repartoDAO).aggiungiLibroReparto(reparto, "ISBN-000");
        verify(response).sendRedirect("gestisci-reparti");
    }

    /**
     * Test with very large idReparto
     * Expected: processes the request correctly
     */
    @Test
    void testDoGet_LargeIdReparto() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("999999");
        when(request.getParameterValues("isbn")).thenReturn(new String[]{"ISBN-LARGE"});

        Reparto reparto = new Reparto();
        reparto.setIdReparto(999999);

        when(repartoDAO.doRetrieveById(999999)).thenReturn(reparto);
        doNothing().when(repartoDAO).aggiungiLibroReparto(any(Reparto.class), anyString());

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        verify(repartoDAO).doRetrieveById(999999);
        verify(repartoDAO).aggiungiLibroReparto(reparto, "ISBN-LARGE");
        verify(response).sendRedirect("gestisci-reparti");
    }

    /**
     * Test that doRetrieveById is called for each book (inefficient but current behavior)
     * Expected: doRetrieveById called N times for N books
     */
    @Test
    void testDoGet_RetrievesRepartoForEachBook() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("5");
        when(request.getParameterValues("isbn")).thenReturn(new String[]{
            "ISBN-1",
            "ISBN-2",
            "ISBN-3",
            "ISBN-4",
            "ISBN-5"
        });

        Reparto reparto = new Reparto();
        reparto.setIdReparto(5);

        when(repartoDAO.doRetrieveById(5)).thenReturn(reparto);
        doNothing().when(repartoDAO).aggiungiLibroReparto(any(Reparto.class), anyString());

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        // Current implementation retrieves reparto for EACH book (inefficient)
        verify(repartoDAO, times(5)).doRetrieveById(5);
        verify(repartoDAO, times(5)).aggiungiLibroReparto(eq(reparto), anyString());
        verify(response).sendRedirect("gestisci-reparti");
    }

    /**
     * Test with special characters in ISBN
     * Expected: special characters are preserved
     */
    @Test
    void testDoGet_SpecialCharactersInISBN() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("6");
        when(request.getParameterValues("isbn")).thenReturn(new String[]{
            "ISBN-978-3-16-148410-0"
        });

        Reparto reparto = new Reparto();
        reparto.setIdReparto(6);

        when(repartoDAO.doRetrieveById(6)).thenReturn(reparto);
        doNothing().when(repartoDAO).aggiungiLibroReparto(any(Reparto.class), anyString());

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        verify(repartoDAO).aggiungiLibroReparto(reparto, "ISBN-978-3-16-148410-0");
        verify(response).sendRedirect("gestisci-reparti");
    }

    /**
     * Test with empty string ISBN
     * Expected: empty string is passed to DAO (validation should be in DAO or elsewhere)
     */
    @Test
    void testDoGet_EmptyStringISBN() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("7");
        when(request.getParameterValues("isbn")).thenReturn(new String[]{""});

        Reparto reparto = new Reparto();
        reparto.setIdReparto(7);

        when(repartoDAO.doRetrieveById(7)).thenReturn(reparto);
        doNothing().when(repartoDAO).aggiungiLibroReparto(any(Reparto.class), anyString());

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        verify(repartoDAO).aggiungiLibroReparto(reparto, "");
        verify(response).sendRedirect("gestisci-reparti");
    }

    /**
     * Test with whitespace-only ISBN
     * Expected: whitespace is passed as-is (no trimming in current implementation)
     */
    @Test
    void testDoGet_WhitespaceOnlyISBN() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("8");
        when(request.getParameterValues("isbn")).thenReturn(new String[]{"   "});

        Reparto reparto = new Reparto();
        reparto.setIdReparto(8);

        when(repartoDAO.doRetrieveById(8)).thenReturn(reparto);
        doNothing().when(repartoDAO).aggiungiLibroReparto(any(Reparto.class), anyString());

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        verify(repartoDAO).aggiungiLibroReparto(reparto, "   ");
        verify(response).sendRedirect("gestisci-reparti");
    }

    /**
     * Test with duplicate ISBNs in the array
     * Expected: aggiungiLibroReparto called for each, even duplicates
     */
    @Test
    void testDoGet_DuplicateISBNs() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("9");
        when(request.getParameterValues("isbn")).thenReturn(new String[]{
            "ISBN-DUP",
            "ISBN-DUP",
            "ISBN-DUP"
        });

        Reparto reparto = new Reparto();
        reparto.setIdReparto(9);

        when(repartoDAO.doRetrieveById(9)).thenReturn(reparto);
        doNothing().when(repartoDAO).aggiungiLibroReparto(any(Reparto.class), anyString());

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        // Current implementation doesn't check for duplicates
        verify(repartoDAO, times(3)).aggiungiLibroReparto(reparto, "ISBN-DUP");
        verify(response).sendRedirect("gestisci-reparti");
    }

    /**
     * Test that redirect always happens regardless of success or failure
     * Expected: redirect is always called
     */
    @Test
    void testDoGet_AlwaysRedirects() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("10");
        when(request.getParameterValues("isbn")).thenReturn(null);

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        verify(response).sendRedirect("gestisci-reparti");
    }

    /**
     * Test dependency injection works correctly
     * Expected: uses injected DAO instead of creating new one
     */
    @Test
    void testDoGet_UsesDependencyInjection() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("20");
        when(request.getParameterValues("isbn")).thenReturn(new String[]{"TEST-ISBN"});

        Reparto reparto = new Reparto();
        reparto.setIdReparto(20);

        when(repartoDAO.doRetrieveById(20)).thenReturn(reparto);
        doNothing().when(repartoDAO).aggiungiLibroReparto(any(Reparto.class), anyString());

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        // Verify the injected mock was used
        verify(repartoDAO).doRetrieveById(20);
        verify(repartoDAO).aggiungiLibroReparto(reparto, "TEST-ISBN");
        verify(response).sendRedirect("gestisci-reparti");
    }

    /**
     * Test with very long ISBN
     * Expected: long ISBN is accepted
     */
    @Test
    void testDoGet_VeryLongISBN() throws Exception {
        String longISBN = "ISBN-" + "1234567890".repeat(10);
        
        when(request.getParameter("idReparto")).thenReturn("30");
        when(request.getParameterValues("isbn")).thenReturn(new String[]{longISBN});

        Reparto reparto = new Reparto();
        reparto.setIdReparto(30);

        when(repartoDAO.doRetrieveById(30)).thenReturn(reparto);
        doNothing().when(repartoDAO).aggiungiLibroReparto(any(Reparto.class), anyString());

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        verify(repartoDAO).aggiungiLibroReparto(reparto, longISBN);
        verify(response).sendRedirect("gestisci-reparti");
    }

    /**
     * Test when doRetrieveById returns null
     * Expected: null is passed to aggiungiLibroReparto (no validation in servlet)
     */
    @Test
    void testDoGet_RepartoNotFound() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("99");
        when(request.getParameterValues("isbn")).thenReturn(new String[]{"ISBN-123"});

        when(repartoDAO.doRetrieveById(99)).thenReturn(null);
        doNothing().when(repartoDAO).aggiungiLibroReparto(any(), anyString());

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        // Current implementation doesn't validate, passes null to DAO
        verify(repartoDAO).doRetrieveById(99);
        verify(repartoDAO).aggiungiLibroReparto(null, "ISBN-123");
        verify(response).sendRedirect("gestisci-reparti");
    }
}
